"""CLI entry point for sorry-graph."""

import argparse
import json
import sys
from pathlib import Path

from ..common import (
    add_export_timeout_arg,
    detect_root_module,
    export_timeout_from_args,
    find_by_module,
    find_decl,
    log,
    module_short,
)
from ..export import (
    EXPORT_DECLS_LEAN,
    export_cached,
    load_from_file,
    recompute_transitive_sorry,
)
from .tracker import (
    TrackerResult,
    analyze_scope,
    analyze_target,
    build_index,
)


def _print_result(result: TrackerResult, root_module: str = "") -> None:
    """Print analysis result to stdout."""
    if not result.sorry_leaves and not result.axioms:
        print(f"{result.target}: sorry-free ({result.total_deps} deps)")
        return

    print(f"{result.target}: "
          f"{len(result.sorry_leaves)} sorry, "
          f"{result.total_deps} deps")

    if result.axioms:
        print(f"\n!! {len(result.axioms)} axiom(s) !!")
        for a in result.axioms:
            print(f"  {a}")

    if result.sorry_leaves:
        print()
        for leaf in result.sorry_leaves:
            mod = module_short(leaf.module, root_module)
            loc = f":{leaf.line}" if leaf.line else ""
            private = " [private]" if leaf.is_private else ""
            print(f"  {leaf.name}{private}")
            if leaf.file:
                print(f"    {leaf.file}{loc}")
            else:
                print(f"    {mod}{loc}")

    if result.graph:
        print(f"\n{result.graph}")


def _print_json(result: TrackerResult) -> None:
    """Print result as JSON to stdout."""
    print(json.dumps({
        "target": result.target,
        "sorry_leaves": [
            {"name": l.name, "module": l.module, "file": l.file,
             "line": l.line, "is_private": l.is_private}
            for l in result.sorry_leaves
        ],
        "total_deps": result.total_deps,
        "axioms": result.axioms,
        "graph": result.graph,
    }, indent=2))


def _load_index(args, lake_root, root_module, parser):
    """Load declaration database and build index."""
    if args.load:
        log(f"Loading from {args.load}...")
        data = load_from_file(Path(args.load))
    else:
        cache_path = lake_root / ".lake" / "decls_cache.json"
        data = export_cached(
            lake_root,
            root_module,
            cache_path,
            EXPORT_DECLS_LEAN,
            timeout=export_timeout_from_args(args, parser),
        )

    recompute_transitive_sorry(data)

    if args.save:
        Path(args.save).write_text(json.dumps(data, indent=2) + "\n")
        log(f"Saved to {args.save}")

    index = build_index(data)
    log(f"Loaded {len(index)} declarations")
    return index


def main():
    parser = argparse.ArgumentParser(
        prog="sorry-graph",
        description="Sorry dependency tracker for Lean 4 projects",
    )
    parser.add_argument(
        "target", nargs="?",
        help="Declaration name (exact or suffix match)",
    )
    parser.add_argument(
        "--file", "-f",
        help="Sorry graph for a file/module (e.g., InfoTheory/Measurement/POVM)",
    )
    parser.add_argument(
        "--all", "-a", action="store_true",
        help="Project-wide sorry summary",
    )
    parser.add_argument(
        "--project", "-p", default=".",
        help="Path to Lean project root (default: current directory)",
    )
    parser.add_argument(
        "--module", "-m",
        help="Root module name (auto-detected from lakefile if omitted)",
    )
    parser.add_argument(
        "--load", "-l",
        help="Load from existing decls.json instead of running ExportDecls",
    )
    parser.add_argument(
        "--save", "-s",
        help="Save exported JSON to file (for reuse with --load)",
    )
    parser.add_argument(
        "--no-graph", action="store_true",
        help="Skip dependency graph rendering",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output results as JSON",
    )
    add_export_timeout_arg(parser)
    args = parser.parse_args()

    if not args.target and not args.file and not args.all:
        parser.print_help()
        print("\nExamples:")
        print("  sorry-graph holevo_bound")
        print("  sorry-graph -f InfoTheory/Measurement/POVM")
        print("  sorry-graph --all")
        sys.exit(1)

    lake_root = Path(args.project).resolve()
    root_module = args.module or detect_root_module(lake_root)
    if not root_module:
        log("ERROR: Could not detect root module. Use --module.")
        sys.exit(1)

    index = _load_index(args, lake_root, root_module, parser)

    # --- File/module scope ---
    if args.file:
        decls = find_by_module(index, args.file, root_module)
        if not decls:
            log(f"No declarations found in module matching '{args.file}'")
            sys.exit(1)

        mod = decls[0].module
        sorry = [d for d in decls if d.has_sorry]
        proven = [d for d in decls if not d.has_sorry]

        log(f"{module_short(mod, root_module)}: "
            f"{len(decls)} declarations ({len(proven)} proven, {len(sorry)} sorry)")

        if not sorry:
            return

        result = analyze_scope(index, decls, show_graph=not args.no_graph,
                               lake_root=str(lake_root))
        if args.json:
            _print_json(result)
        else:
            _print_result(result, root_module)
        return

    # --- Project-wide ---
    if args.all:
        all_decls = list(index.values())
        sorry = [d for d in all_decls if d.has_sorry]
        sorry_direct = [d for d in all_decls if d.contains_sorry]

        log(f"Project: {root_module} — "
            f"{len(all_decls)} declarations, "
            f"{len(sorry_direct)} direct sorry, "
            f"{len(sorry)} transitive sorry")

        if not sorry_direct:
            print("All proven!")
            return

        result = analyze_scope(index, all_decls, show_graph=not args.no_graph,
                               lake_root=str(lake_root))
        if args.json:
            _print_json(result)
        else:
            _print_result(result, root_module)
        return

    # --- Single declaration ---
    matches = find_decl(index, args.target)
    if not matches:
        log(f"Declaration '{args.target}' not found.")
        sys.exit(1)

    for decl in matches:
        result = analyze_target(index, decl.name, show_graph=not args.no_graph,
                                lake_root=str(lake_root))
        if args.json:
            _print_json(result)
        else:
            _print_result(result, root_module)


if __name__ == "__main__":
    main()
