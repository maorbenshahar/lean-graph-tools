"""CLI entry point for sig-tree."""

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
from .tracker import build_index, dep_closure
from .render import render_context


def main(argv: Optional[list[str]] = None) -> None:
    parser = argparse.ArgumentParser(
        prog="sig-tree",
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
                             timeout=export_timeout_from_args(args, parser))

    if args.save:
        Path(args.save).write_text(json.dumps(data, indent=2) + "\n")
        log(f"Saved to {args.save}")

    index = build_index(data)

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
                    "type_signature": d.type_signature,
                    "is_target": d.name in set(target_names),
                    "is_private": d.is_private,
                    "deps": d.deps,
                    **({"line": d.line} if d.line else {}),
                    **({"fields": [{"name": f.name, "type": f.type}
                                   for f in d.fields]} if d.fields else {}),
                    **({"constructors": [{"name": c.name, "type": c.type}
                                         for c in d.constructors]} if d.constructors else {}),
                    **({"value": d.value} if d.value else {}),
                    **({"parents": d.parents} if d.parents else {}),
                    **({"has_sorry": True} if d.has_sorry else {}),
                }
                for d in closure
            ],
        }
        output = json.dumps(result, indent=2)
    else:
        output = render_context(
            targets=targets,
            context=closure,
            root_module=root_module,
            header=header,
        )

    if args.output:
        Path(args.output).write_text(output + "\n")
        log(f"Written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
