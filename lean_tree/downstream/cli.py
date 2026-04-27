"""CLI entry point for downstream-tree."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from ..common import detect_root_module, find_decl, log, module_short
from ..export import (
    EXPORT_DECLS_LEAN,
    export_cached,
    load_from_file,
    recompute_transitive_sorry,
)
from .tracker import (
    DownstreamResult,
    UpstreamResult,
    analyze_downstream,
    analyze_upstream,
    build_index,
    dependency_relation,
    downstream_node_to_json,
)


def _load_index(args, lake_root: Path, root_module: str):
    if args.load:
        log(f"Loading from {args.load}...")
        data = load_from_file(Path(args.load))
    else:
        cache_path = lake_root / ".lake" / "decls_cache.json"
        data = export_cached(lake_root, root_module, cache_path, EXPORT_DECLS_LEAN)

    recompute_transitive_sorry(data)

    if args.save:
        Path(args.save).write_text(json.dumps(data, indent=2) + "\n")
        log(f"Saved to {args.save}")

    index = build_index(data)
    log(f"Loaded {len(index)} declarations")
    return index


def _resolve_one(index, query: str) -> str:
    matches = find_decl(index, query)
    if not matches:
        log(f"Declaration '{query}' not found.")
        sys.exit(1)
    if len(matches) > 1:
        log(f"Ambiguous declaration '{query}', matches:")
        for decl in matches:
            log(f"  {decl.name}")
        sys.exit(1)
    return matches[0].name


def _print_downstream_result(
    result: DownstreamResult,
    root_module: str,
    lake_root: Path,
) -> None:
    if not result.declarations:
        print(f"{result.target}: no downstream declarations")
        return

    print(f"{result.target}: {result.total_downstream} downstream declarations")
    print()
    for node in result.declarations:
        decl = node.decl
        mod = module_short(decl.module, root_module)
        loc = f":{decl.line}" if decl.line else ""
        private = " [private]" if decl.is_private else ""
        sorry = ""
        if decl.contains_sorry:
            sorry = " [contains sorry]"
        elif decl.has_sorry:
            sorry = " [depends on sorry]"
        print(f"  d={node.distance} {decl.kind} {decl.name}{private}{sorry}")
        print(f"    {lake_root / (decl.module.replace('.', '/') + '.lean')}{loc}"
              if decl.module else f"    {mod}{loc}")

    if result.tree:
        print(f"\n{result.tree}")


def _print_upstream_result(
    result: UpstreamResult,
    root_module: str,
    lake_root: Path,
) -> None:
    if not result.declarations:
        print(f"{result.target}: no upstream dependencies")
        return

    print(f"{result.target}: {result.total_upstream} upstream dependencies")
    print()
    for node in result.declarations:
        decl = node.decl
        mod = module_short(decl.module, root_module)
        loc = f":{decl.line}" if decl.line else ""
        private = " [private]" if decl.is_private else ""
        sorry = ""
        if decl.contains_sorry:
            sorry = " [contains sorry]"
        elif decl.has_sorry:
            sorry = " [depends on sorry]"
        print(f"  d={node.distance} {decl.kind} {decl.name}{private}{sorry}")
        print(f"    {lake_root / (decl.module.replace('.', '/') + '.lean')}{loc}"
              if decl.module else f"    {mod}{loc}")

    if result.tree:
        print(f"\n{result.tree}")


def _print_downstream_json(result: DownstreamResult, lake_root: Path) -> None:
    print(json.dumps({
        "target": result.target,
        "total_downstream": result.total_downstream,
        "declarations": [
            downstream_node_to_json(node, str(lake_root))
            for node in result.declarations
        ],
        "tree": result.tree,
    }, indent=2))


def _print_upstream_json(result: UpstreamResult, lake_root: Path) -> None:
    print(json.dumps({
        "target": result.target,
        "total_upstream": result.total_upstream,
        "declarations": [
            downstream_node_to_json(node, str(lake_root))
            for node in result.declarations
        ],
        "tree": result.tree,
    }, indent=2))


def _print_connected_result(result) -> None:
    connected = result.left_depends_on_right or result.right_depends_on_left
    if not connected:
        print(f"No dependency path found between {result.left} and {result.right}.")
        return

    if result.left_depends_on_right:
        print(f"{result.left} depends on {result.right} "
              f"(distance {len(result.left_to_right_path) - 1})")
        print("  " + " -> ".join(result.left_to_right_path))

    if result.right_depends_on_left:
        if result.left_depends_on_right:
            print()
        print(f"{result.right} depends on {result.left} "
              f"(distance {len(result.right_to_left_path) - 1})")
        print("  " + " -> ".join(result.right_to_left_path))


def _print_connected_json(result) -> None:
    print(json.dumps({
        "left": result.left,
        "right": result.right,
        "left_depends_on_right": result.left_depends_on_right,
        "right_depends_on_left": result.right_depends_on_left,
        "left_to_right_path": result.left_to_right_path,
        "right_to_left_path": result.right_to_left_path,
    }, indent=2))


def _add_shared_args(parser: argparse.ArgumentParser) -> None:
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
        "--max-depth", type=int,
        help="Limit dependency distance",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output result as JSON",
    )


def downstream_main() -> None:
    parser = argparse.ArgumentParser(
        prog="downstream-tree",
        description="Reverse dependency tracker for Lean 4 project declarations",
    )
    parser.add_argument(
        "target",
        help="Declaration name (exact or suffix match)",
    )
    parser.add_argument(
        "--direct", action="store_true",
        help="Only show direct downstream users",
    )
    parser.add_argument(
        "--no-tree", action="store_true",
        help="Skip dependency tree rendering",
    )
    _add_shared_args(parser)
    args = parser.parse_args()

    lake_root = Path(args.project).resolve()
    root_module = args.module or detect_root_module(lake_root)
    if not root_module:
        log("ERROR: Could not detect root module. Use --module.")
        sys.exit(1)

    index = _load_index(args, lake_root, root_module)
    target = _resolve_one(index, args.target)
    max_depth = 1 if args.direct else args.max_depth
    result = analyze_downstream(
        index,
        target,
        show_tree=not args.no_tree,
        max_depth=max_depth,
    )
    if args.json:
        _print_downstream_json(result, lake_root)
    else:
        _print_downstream_result(result, root_module, lake_root)


def upstream_main() -> None:
    parser = argparse.ArgumentParser(
        prog="upstream-tree",
        description="Dependency tracker for Lean 4 project declarations",
    )
    parser.add_argument(
        "target",
        help="Declaration name (exact or suffix match)",
    )
    parser.add_argument(
        "--direct", action="store_true",
        help="Only show direct upstream dependencies",
    )
    parser.add_argument(
        "--no-tree", action="store_true",
        help="Skip dependency tree rendering",
    )
    _add_shared_args(parser)
    args = parser.parse_args()

    lake_root = Path(args.project).resolve()
    root_module = args.module or detect_root_module(lake_root)
    if not root_module:
        log("ERROR: Could not detect root module. Use --module.")
        sys.exit(1)

    index = _load_index(args, lake_root, root_module)
    target = _resolve_one(index, args.target)
    max_depth = 1 if args.direct else args.max_depth
    result = analyze_upstream(
        index,
        target,
        show_tree=not args.no_tree,
        max_depth=max_depth,
    )
    if args.json:
        _print_upstream_json(result, lake_root)
    else:
        _print_upstream_result(result, root_module, lake_root)


def connected_main() -> None:
    parser = argparse.ArgumentParser(
        prog="dep-connected",
        description="Check whether either Lean declaration depends on the other",
    )
    parser.add_argument("left", help="First declaration name (exact or suffix match)")
    parser.add_argument("right", help="Second declaration name (exact or suffix match)")
    _add_shared_args(parser)
    args = parser.parse_args()

    lake_root = Path(args.project).resolve()
    root_module = args.module or detect_root_module(lake_root)
    if not root_module:
        log("ERROR: Could not detect root module. Use --module.")
        sys.exit(1)

    index = _load_index(args, lake_root, root_module)
    left = _resolve_one(index, args.left)
    right = _resolve_one(index, args.right)
    result = dependency_relation(index, left, right, max_depth=args.max_depth)
    if args.json:
        _print_connected_json(result)
    else:
        _print_connected_result(result)


def main() -> None:
    downstream_main()


if __name__ == "__main__":
    main()
