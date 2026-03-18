"""Core goal tracking: BFS, sorry detection, tree rendering."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from ..common import _private_short_name, module_short


@dataclass
class DeclInfo:
    """A declaration from the sorry export database."""
    name: str
    kind: str
    module: str
    has_sorry: bool
    contains_sorry: bool
    is_private: bool
    deps: list[str]
    line: Optional[int] = None


def build_index(data: dict) -> dict[str, DeclInfo]:
    """Build a name -> DeclInfo lookup from exported JSON."""
    index = {}
    for d in data["declarations"]:
        index[d["name"]] = DeclInfo(
            name=d["name"],
            kind=d["kind"],
            module=d["module"],
            has_sorry=d["has_sorry"],
            contains_sorry=d["contains_sorry"],
            is_private=d.get("is_private", False),
            deps=d.get("deps", []),
            line=d.get("line"),
        )
    return index


# ---------------------------------------------------------------------------
# BFS and sorry analysis
# ---------------------------------------------------------------------------

def transitive_deps(index: dict[str, DeclInfo], target: str) -> list[DeclInfo]:
    """Compute transitive dependency closure via BFS."""
    visited: set[str] = set()
    queue = [target]
    order: list[DeclInfo] = []

    while queue:
        name = queue.pop(0)
        if name in visited:
            continue
        visited.add(name)
        if name in index:
            order.append(index[name])
            for dep in index[name].deps:
                if dep not in visited:
                    queue.append(dep)

    return order


def has_transitive_sorry(name: str, index: dict[str, DeclInfo],
                         memo: Optional[dict[str, bool]] = None) -> bool:
    """Check if a declaration has sorry or depends transitively on one."""
    if memo is None:
        memo = {}
    if name in memo:
        return memo[name]
    if name not in index:
        memo[name] = False
        return False

    decl = index[name]
    if decl.has_sorry or decl.kind == "axiom":
        memo[name] = True
        return True

    # Prevent infinite recursion on cycles
    memo[name] = False
    for dep in decl.deps:
        if has_transitive_sorry(dep, index, memo):
            memo[name] = True
            return True

    return False


def module_to_path(module: str, lake_root: Optional[str] = None) -> str:
    """Convert a Lean module name to a relative file path.

    e.g. 'QuantumInformation.Math.Foo' -> 'QuantumInformation/Math/Foo.lean'
    If lake_root is provided, returns an absolute path.
    """
    rel = module.replace(".", "/") + ".lean"
    if lake_root:
        from pathlib import Path
        return str(Path(lake_root) / rel)
    return rel


@dataclass
class SorryLeaf:
    """A declaration with explicit sorry in the dependency tree."""
    name: str
    module: str
    file: str = ""
    line: Optional[int] = None
    is_private: bool = False


@dataclass
class TrackerResult:
    """Result of analyzing a target declaration."""
    target: str
    sorry_leaves: list[SorryLeaf]
    total_deps: int
    tree: str = ""
    axioms: list[str] = field(default_factory=list)


def analyze_target(index: dict[str, DeclInfo], target: str,
                   show_tree: bool = True,
                   lake_root: Optional[str] = None) -> TrackerResult:
    """Analyze a target declaration and return its sorry dependency info."""
    closure = transitive_deps(index, target)
    closure_index = {d.name: d for d in closure}

    # Compute transitive sorry status
    memo: dict[str, bool] = {}
    for d in closure:
        has_transitive_sorry(d.name, closure_index, memo)

    # Find axioms
    axioms = [d.name for d in closure if d.kind == "axiom"]

    # Find sorry leaves (explicit sorry)
    sorry_leaves = []
    for d in closure:
        if d.contains_sorry:
            sorry_leaves.append(SorryLeaf(
                name=d.name, module=d.module,
                file=module_to_path(d.module, lake_root),
                line=d.line, is_private=d.is_private,
            ))

    tree = ""
    if show_tree and (sorry_leaves or axioms):
        tree = render_tree(target, closure_index, memo)

    return TrackerResult(
        target=target,
        sorry_leaves=sorry_leaves,
        total_deps=len(closure),
        tree=tree,
        axioms=axioms,
    )


def analyze_scope(index: dict[str, DeclInfo], decls: list[DeclInfo],
                  show_tree: bool = True,
                  lake_root: Optional[str] = None) -> TrackerResult:
    """Analyze a scope (file/module/project) -- union of sorry trees.

    Treats the scope as a virtual root: collects all sorry leaves reachable
    from any declaration in the scope, deduplicates, and renders a combined tree
    with shared visited set (so subtrees aren't repeated).
    """
    all_sorry_leaves: dict[str, SorryLeaf] = {}
    all_axioms: set[str] = set()
    all_closure_names: set[str] = set()
    sorry_decl_names: list[str] = []

    for d in decls:
        if not d.has_sorry:
            continue
        result = analyze_target(index, d.name, show_tree=False, lake_root=lake_root)
        for leaf in result.sorry_leaves:
            all_sorry_leaves[leaf.name] = leaf
        all_axioms.update(result.axioms)
        all_closure_names.update(d2.name for d2 in transitive_deps(index, d.name))
        sorry_decl_names.append(d.name)

    sorry_leaves = list(all_sorry_leaves.values())

    tree = ""
    if show_tree and sorry_decl_names and (sorry_leaves or all_axioms):
        # Build combined closure + memo for rendering
        combined_index: dict[str, DeclInfo] = {}
        for name in sorry_decl_names:
            for d2 in transitive_deps(index, name):
                combined_index[d2.name] = d2
        memo: dict[str, bool] = {}
        for d2 in combined_index.values():
            has_transitive_sorry(d2.name, combined_index, memo)

        tree = render_scope_tree(sorry_decl_names, combined_index, memo)

    return TrackerResult(
        target=f"[{len(decls)} declarations]",
        sorry_leaves=sorry_leaves,
        total_deps=len(all_closure_names),
        tree=tree,
        axioms=sorted(all_axioms),
    )


# ---------------------------------------------------------------------------
# Tree rendering
# ---------------------------------------------------------------------------

def display_name(decl: DeclInfo) -> str:
    """Get a readable display name for a declaration."""
    if decl.is_private:
        short = _private_short_name(decl.name)
        if short:
            return short + " [private]"
    return decl.name


def _render_tree(roots: list[str], index: dict[str, DeclInfo],
                 memo: dict[str, bool]) -> str:
    """Render ASCII dependency tree showing sorry branches."""
    lines: list[str] = []
    visited: set[str] = set()

    def _walk(name: str, prefix: str, is_last: bool) -> None:
        connector = "\u2514\u2500 " if is_last else "\u251c\u2500 "

        if name in visited:
            label = display_name(index[name]) if name in index else name
            lines.append(f"{prefix}{connector}{label} (see above)")
            return
        visited.add(name)

        if name not in index:
            return

        decl = index[name]
        issue_deps = [dep for dep in decl.deps if memo.get(dep, False)]

        tag = ""
        if decl.contains_sorry:
            tag = " [sorry]"
        elif decl.kind == "axiom":
            tag = " [AXIOM]"

        lines.append(f"{prefix}{connector}{display_name(decl)}{tag}")

        if not issue_deps:
            return

        extension = "   " if is_last else "\u2502  "
        new_prefix = prefix + extension
        for i, dep in enumerate(issue_deps):
            _walk(dep, new_prefix, i == len(issue_deps) - 1)

    for root in roots:
        _walk(root, "", True)

    return "\n".join(lines)


def render_tree(target: str, index: dict[str, DeclInfo],
                memo: dict[str, bool]) -> str:
    """Render an ASCII dependency tree showing sorry branches."""
    return _render_tree([target], index, memo)


def render_scope_tree(roots: list[str], index: dict[str, DeclInfo],
                      memo: dict[str, bool]) -> str:
    """Render combined sorry tree for multiple roots, sharing visited set."""
    return _render_tree(roots, index, memo)
