"""CLI entry point for sig-graph."""

import argparse
import json
import sys
from pathlib import Path
from typing import Optional

from ..common import (
    add_export_timeout_arg,
    detect_root_module,
    export_timeout_from_args,
    find_by_module,
    find_decl,
    log,
)
from ..export import EXPORT_SIGS_LEAN, export_cached, load_from_file
from .tracker import SigData, build_index, dep_closure
from .render import comparator_config, render_digest


def main(argv: Optional[list[str]] = None) -> None:
    parser = argparse.ArgumentParser(
        prog="sig-graph",
        description="Extract type signature context for Lean 4 auditors.",
    )

    parser.add_argument("names", nargs="*",
                        help="Declaration names to extract context for")
    parser.add_argument("-f", "--file", type=str,
                        help="Extract context for all declarations in a file/module")
    parser.add_argument("-p", "--project", type=str, default=".",
                        help="Lean project root (default: current directory)")
    parser.add_argument("-m", "--module", type=str,
                        help="Root module name (auto-detected if not specified)")
    parser.add_argument("-l", "--load", type=str,
                        help="Load from a previously saved JSON export")
    parser.add_argument("-s", "--save", type=str,
                        help="Save the export to a JSON file")
    parser.add_argument("-o", "--output", type=str,
                        help="Write output to file instead of stdout")
    parser.add_argument("--json", action="store_true",
                        help="Output raw JSON instead of rendered context")
    parser.add_argument("--no-context", action="store_true",
                        help="Show only target declarations, skip dependencies")
    parser.add_argument("--rebuild-cache", action="store_true",
                        help="Force a full re-export instead of the incremental partial rebuild")
    parser.add_argument("--comparator", action="store_true",
                        help="Emit a leanprover/comparator Challenge (import real deps; "
                             "targets sorried) plus a sibling config.json")
    parser.add_argument("--print", dest="print_mode", action="store_true",
                        help="Render the 'print' digest (this is the DEFAULT): import the "
                             "real closure modules, show a dependency tree + per-decl "
                             "docstring + verbatim source slice + #check/#print of the "
                             "imported decl (elaborated ground truth, for comparison).")
    parser.add_argument("--no-source", dest="no_source", action="store_true",
                        help="In 'print' mode, omit the authored source slice (keep the "
                             "dependency tree + #check/#print only).")
    parser.add_argument("--self-contained", dest="self_contained", action="store_true",
                        help="Render the standalone self-contained mini-library (closure "
                             "re-declared as live source, compiles without the library) "
                             "instead of the default 'print' digest.")
    parser.add_argument("--connected", action="store_true",
                        help="Render the 'connected' mini-replica (one Audit namespace, "
                             "closure wired leaf-first) instead of the default self-contained "
                             "mini-library. Breaks on project notation.")
    parser.add_argument("--import-copies", dest="import_copies", action="store_true",
                        help="Fallback render: each decl isolated in its own namespace "
                             "(target first), resolving to the real imports. Compiles even "
                             "for notation-heavy closures, but decls aren't wired together. "
                             "Default is the self-contained mini-library.")
    parser.add_argument("--config-out", type=str,
                        help="Path for the comparator config.json (default: config.json "
                             "beside -o)")
    parser.add_argument("--challenge-module", type=str,
                        help="Override the comparator config challenge_module")
    parser.add_argument("--permitted-axioms", type=str,
                        default="Classical.choice,Quot.sound,propext",
                        help="Comma-separated permitted axioms for comparator config.json")
    add_export_timeout_arg(parser)

    args = parser.parse_args(argv)

    lake_root = Path(args.project).resolve()

    # Load or export
    if args.load:
        data = load_from_file(Path(args.load))
        root_module = data.get("root_module", "")
    else:
        root_module = args.module or detect_root_module(lake_root)
        if not root_module:
            print("ERROR: Could not detect root module. Use -m <RootModule>.",
                  file=sys.stderr)
            sys.exit(1)

        cache_path = lake_root / ".lake" / "sigs_cache.json"
        data = export_cached(lake_root, root_module, cache_path,
                             EXPORT_SIGS_LEAN,
                             timeout=export_timeout_from_args(args, parser),
                             force_full=args.rebuild_cache)

    if args.save:
        Path(args.save).write_text(json.dumps(data, indent=2) + "\n")
        log(f"Saved to {args.save}")

    sig = SigData(data)
    index = sig.index
    if not root_module:
        root_module = sig.root_module

    # Find target declarations
    if args.file:
        targets = find_by_module(index, args.file, root_module)
        if not targets:
            print(f"No declarations found for module/file: {args.file}",
                  file=sys.stderr)
            sys.exit(1)
        header = args.file
    elif args.names:
        targets = []
        for name in args.names:
            found = find_decl(index, name)
            if not found:
                print(f"WARNING: Declaration not found: {name}", file=sys.stderr)
            targets.extend(found)
        if not targets:
            print("ERROR: No declarations found.", file=sys.stderr)
            sys.exit(1)
        header = ", ".join(args.names)
    else:
        parser.print_help()
        sys.exit(1)

    # Compute closure
    target_names = [d.name for d in targets]

    if args.no_context:
        closure = targets
    else:
        closure = dep_closure(index, target_names)

    if args.json:
        result = {
            "targets": target_names,
            "closure_size": len(closure),
            "declarations": [
                {
                    "name": d.name,
                    "kind": d.kind,
                    "module": d.module,
                    "is_target": d.name in set(target_names),
                    "is_private": d.is_private,
                    "deps": d.deps,
                    **({"line": d.line} if d.line else {}),
                    **({"fields": [{"name": f.name, "proj_name": f.proj_name}
                                   for f in d.fields]} if d.fields else {}),
                    **({"parents": d.parents} if d.parents else {}),
                    **({"has_sorry": True} if d.has_sorry else {}),
                    **({"source_text": d.source_text} if d.source_text else {}),
                    **({"decl_namespace": d.decl_namespace} if d.decl_namespace else {}),
                }
                for d in closure
            ],
        }
        output = json.dumps(result, indent=2)
    else:
        if not sig.has_source_text:
            print("ERROR: this export predates the source-slice fields (no source_text). "
                  "Re-run without --load, or with --rebuild-cache, to regenerate the cache.",
                  file=sys.stderr)
            sys.exit(1)
        mode = ("comparator" if args.comparator
                else "import_copies" if args.import_copies
                else "connected" if args.connected
                else "self_contained" if args.self_contained
                else "print")
        output = render_digest(
            targets=targets,
            closure=closure,
            index=index,
            root_module=root_module,
            module_imports=sig.module_imports,
            module_opens=sig.module_opens,
            module_notations=sig.module_notations,
            module_variables=sig.module_variables,
            module_context=sig.module_context,
            project_modules=sig.project_modules,
            mode=mode,
            header=header,
            show_source=not args.no_source,
        )

    if args.output:
        Path(args.output).write_text(output + "\n")
        log(f"Written to {args.output}")
    else:
        print(output)

    # Comparator: emit the sibling config.json next to the digest.
    if args.comparator and not args.json:
        if args.config_out:
            config_path = Path(args.config_out)
        elif args.output:
            config_path = Path(args.output).with_name("config.json")
        else:
            config_path = Path("config.json")
        challenge_module = args.challenge_module or (
            Path(args.output).stem.split(".")[0] if args.output else "Challenge")
        cfg = comparator_config(
            targets, closure,
            challenge_module=challenge_module,
            permitted_axioms=[a.strip() for a in args.permitted_axioms.split(",") if a.strip()],
        )
        config_path.write_text(json.dumps(cfg, indent=2) + "\n")
        log(f"Wrote comparator config to {config_path}")


if __name__ == "__main__":
    main()
