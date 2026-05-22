"""Reverse dependency tracking for Lean declaration export data."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from ..common import _private_short_name
from ..graph import DeclarationGraph, Direction
from ..sorry.tracker import DeclInfo, build_index, module_to_path


@dataclass
class DownstreamNode:
    """A declaration reachable through dependency graph edges."""

    decl: DeclInfo
    distance: int


@dataclass
class DownstreamResult:
    """Result of downstream analysis for a target declaration."""

    target: str
    declarations: list[DownstreamNode]
    total_downstream: int
    graph: str = ""


@dataclass
class UpstreamResult:
    """Result of upstream dependency analysis for a target declaration."""

    target: str
    declarations: list[DownstreamNode]
    total_upstream: int
    graph: str = ""


@dataclass
class DependencyPathResult:
    """Dependency connectivity result for two declarations."""

    left: str
    right: str
    left_depends_on_right: bool
    right_depends_on_left: bool
    left_to_right_path: list[str] = field(default_factory=list)
    right_to_left_path: list[str] = field(default_factory=list)


def build_reverse_index(index: dict[str, DeclInfo]) -> dict[str, list[str]]:
    """Build dep -> declarations that directly use dep."""
    return DeclarationGraph(index).reverse


def downstream_closure(
    index: dict[str, DeclInfo],
    target: str,
    max_depth: Optional[int] = None,
    graph: DeclarationGraph | None = None,
) -> list[DownstreamNode]:
    """Compute all declarations that transitively depend on target.

    The returned list excludes the target itself and is ordered by BFS distance
    through reverse dependency edges.
    """
    graph = graph or DeclarationGraph(index)
    return [
        DownstreamNode(index[node.name], node.distance)
        for node in graph.closure([target], "dependents", max_depth=max_depth)
    ]


def upstream_closure(
    index: dict[str, DeclInfo],
    target: str,
    max_depth: Optional[int] = None,
    graph: DeclarationGraph | None = None,
) -> list[DownstreamNode]:
    """Compute all declarations that target transitively depends on."""
    graph = graph or DeclarationGraph(index)
    return [
        DownstreamNode(index[node.name], node.distance)
        for node in graph.closure([target], "dependencies", max_depth=max_depth)
    ]


def analyze_downstream(
    index: dict[str, DeclInfo],
    target: str,
    show_graph: bool = True,
    max_depth: Optional[int] = None,
) -> DownstreamResult:
    """Analyze all downstream declarations of target."""
    graph = DeclarationGraph(index)
    nodes = downstream_closure(index, target, max_depth=max_depth, graph=graph)
    rendered = (
        render_downstream_graph(index, target, max_depth=max_depth, graph=graph)
        if show_graph else ""
    )
    return DownstreamResult(
        target=target,
        declarations=nodes,
        total_downstream=len(nodes),
        graph=rendered,
    )


def analyze_upstream(
    index: dict[str, DeclInfo],
    target: str,
    show_graph: bool = True,
    max_depth: Optional[int] = None,
) -> UpstreamResult:
    """Analyze all upstream dependencies of target."""
    graph = DeclarationGraph(index)
    nodes = upstream_closure(index, target, max_depth=max_depth, graph=graph)
    rendered = (
        render_dependency_graph(
            index,
            target,
            "dependencies",
            max_depth=max_depth,
            graph=graph,
        )
        if show_graph else ""
    )
    return UpstreamResult(
        target=target,
        declarations=nodes,
        total_upstream=len(nodes),
        graph=rendered,
    )


def find_dependency_path(
    index: dict[str, DeclInfo],
    source: str,
    target: str,
    max_depth: Optional[int] = None,
) -> list[str]:
    """Return a shortest dependency path source -> ... -> target, if any."""
    return DeclarationGraph(index).shortest_path(
        source,
        target,
        "dependencies",
        max_depth=max_depth,
    )


def dependency_relation(
    index: dict[str, DeclInfo],
    left: str,
    right: str,
    max_depth: Optional[int] = None,
) -> DependencyPathResult:
    """Check both dependency directions between two declarations."""
    left_path = find_dependency_path(index, left, right, max_depth=max_depth)
    right_path = find_dependency_path(index, right, left, max_depth=max_depth)
    return DependencyPathResult(
        left=left,
        right=right,
        left_depends_on_right=bool(left_path),
        right_depends_on_left=bool(right_path),
        left_to_right_path=left_path,
        right_to_left_path=right_path,
    )


def display_name(decl: DeclInfo) -> str:
    """Get a readable display name for a declaration."""
    if decl.is_private:
        short = _private_short_name(decl.name)
        if short:
            return short + " [private]"
    return decl.name


def render_downstream_graph(
    index: dict[str, DeclInfo],
    target: str,
    max_depth: Optional[int] = None,
    graph: DeclarationGraph | None = None,
) -> str:
    """Render a reverse dependency graph rooted at target."""
    return render_dependency_graph(
        index,
        target,
        "dependents",
        max_depth=max_depth,
        graph=graph,
    )


def render_dependency_graph(
    index: dict[str, DeclInfo],
    target: str,
    direction: Direction,
    max_depth: Optional[int] = None,
    graph: DeclarationGraph | None = None,
) -> str:
    """Render a dependency graph rooted at target in either edge direction."""
    graph = graph or DeclarationGraph(index)
    lines: list[str] = []
    visited: set[str] = set()

    def _tag(decl: DeclInfo) -> str:
        tags = [decl.kind]
        if decl.contains_sorry:
            tags.append("contains sorry")
        elif decl.has_sorry:
            tags.append("depends on sorry")
        return " [" + ", ".join(tags) + "]"

    def _walk(name: str, prefix: str, is_last: bool, depth: int) -> None:
        connector = "└─ " if is_last else "├─ "
        if name not in index:
            lines.append(f"{prefix}{connector}{name}")
            return

        decl = index[name]
        if name in visited:
            lines.append(f"{prefix}{connector}{display_name(decl)} (see above)")
            return
        visited.add(name)
        lines.append(f"{prefix}{connector}{display_name(decl)}{_tag(decl)}")

        if max_depth is not None and depth >= max_depth:
            return

        children = graph.neighbors(name, direction)
        extension = "   " if is_last else "│  "
        new_prefix = prefix + extension
        for i, child in enumerate(children):
            _walk(child, new_prefix, i == len(children) - 1, depth + 1)

    _walk(target, "", True, 0)
    return "\n".join(lines)


def downstream_node_to_json(node: DownstreamNode, lake_root: Optional[str] = None) -> dict:
    """Convert a downstream node to JSON-serializable data."""
    decl = node.decl
    return {
        "name": decl.name,
        "kind": decl.kind,
        "module": decl.module,
        "file": module_to_path(decl.module, lake_root) if decl.module else "",
        "line": decl.line,
        "is_private": decl.is_private,
        "has_sorry": decl.has_sorry,
        "contains_sorry": decl.contains_sorry,
        "distance": node.distance,
    }
