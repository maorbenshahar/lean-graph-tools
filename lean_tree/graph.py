"""Shared declaration graph queries.

Edges point in the natural dependency direction:

    user declaration -> declaration it depends on

Reverse queries use the same graph with edges traversed backward.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Literal, Protocol


Direction = Literal["dependencies", "dependents"]


class HasDeps(Protocol):
    """Minimal declaration shape needed by graph searches."""

    name: str
    deps: list[str]


@dataclass(frozen=True)
class ReachableNode:
    """A graph node reached by BFS."""

    name: str
    distance: int


class DeclarationGraph:
    """Directed graph of Lean declarations.

    The graph is built from a declaration index once, then supports forward
    dependency queries, reverse downstream queries, and shortest paths.
    """

    def __init__(self, index: dict[str, HasDeps]):
        self.index = index
        self.forward: dict[str, list[str]] = {
            name: [dep for dep in decl.deps if dep in index]
            for name, decl in index.items()
        }
        self._reverse: dict[str, list[str]] | None = None

    @property
    def reverse(self) -> dict[str, list[str]]:
        """Reverse adjacency map, built lazily for downstream queries."""
        if self._reverse is None:
            reverse: dict[str, list[str]] = {}
            for name, deps in self.forward.items():
                for dep in deps:
                    reverse.setdefault(dep, []).append(name)
            self._reverse = reverse
        return self._reverse

    def closure_names(
        self,
        roots: list[str],
        direction: Direction,
        max_depth: int | None = None,
        include_roots: bool = False,
    ) -> list[str]:
        """BFS closure returning names only.

        This is the fast path for tools that do not need distances.
        """
        visited: set[str] = set()
        queue: deque[tuple[str, int]] = deque()
        result: list[str] = []

        for root in roots:
            if root not in self.index or root in visited:
                continue
            visited.add(root)
            queue.append((root, 0))
            if include_roots:
                result.append(root)

        while queue:
            name, depth = queue.popleft()
            if max_depth is not None and depth >= max_depth:
                continue
            for child in self.neighbors(name, direction):
                if child in visited:
                    continue
                visited.add(child)
                result.append(child)
                queue.append((child, depth + 1))

        return result

    def neighbors(self, name: str, direction: Direction) -> list[str]:
        """Return adjacent declarations in the requested direction."""
        if direction == "dependencies":
            return self.forward.get(name, [])
        return self.reverse.get(name, [])

    def closure(
        self,
        roots: list[str],
        direction: Direction,
        max_depth: int | None = None,
        include_roots: bool = False,
    ) -> list[ReachableNode]:
        """BFS closure from one or more roots.

        Cycles and diamonds are handled by a visited set. Roots may be a single
        declaration or a virtual multi-root set.
        """
        visited: set[str] = set()
        queue: deque[tuple[str, int]] = deque()
        result: list[ReachableNode] = []

        for root in roots:
            if root not in self.index or root in visited:
                continue
            visited.add(root)
            queue.append((root, 0))
            if include_roots:
                result.append(ReachableNode(root, 0))

        while queue:
            name, depth = queue.popleft()
            if max_depth is not None and depth >= max_depth:
                continue
            for child in self.neighbors(name, direction):
                if child in visited:
                    continue
                visited.add(child)
                child_depth = depth + 1
                result.append(ReachableNode(child, child_depth))
                queue.append((child, child_depth))

        return result

    def shortest_path(
        self,
        source: str,
        target: str,
        direction: Direction = "dependencies",
        max_depth: int | None = None,
    ) -> list[str]:
        """Return a shortest path in the requested direction, if one exists."""
        if source not in self.index or target not in self.index:
            return []
        if source == target:
            return [source]

        queue: deque[tuple[str, int]] = deque([(source, 0)])
        visited: set[str] = {source}
        parent: dict[str, str] = {}

        while queue:
            name, depth = queue.popleft()
            if max_depth is not None and depth >= max_depth:
                continue
            for child in self.neighbors(name, direction):
                if child in visited:
                    continue
                visited.add(child)
                parent[child] = name
                if child == target:
                    return _reconstruct_path(parent, source, target)
                queue.append((child, depth + 1))

        return []


def _reconstruct_path(parent: dict[str, str], source: str, target: str) -> list[str]:
    path = [target]
    cur = target
    while cur != source:
        cur = parent[cur]
        path.append(cur)
    path.reverse()
    return path
