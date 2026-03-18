"""Core declaration tracking: index, BFS on type-level deps."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from ..common import _private_short_name, module_short


@dataclass
class FieldInfo:
    """A structure field."""
    name: str
    type: str
    proj_name: str = ""
    from_parent: bool = False


@dataclass
class CtorInfo:
    """An inductive constructor."""
    name: str
    type: str


@dataclass
class DeclInfo:
    """A declaration with its type signature and metadata."""
    name: str
    kind: str
    module: str
    is_private: bool
    type_signature: str
    deps: list[str]
    line: Optional[int] = None
    fields: Optional[list[FieldInfo]] = None
    constructors: Optional[list[CtorInfo]] = None
    value: Optional[str] = None  # For abbrevs
    parents: Optional[list[str]] = None  # Parent structure names (from extends)
    has_sorry: bool = False
    docstring: Optional[str] = None


def build_index(data: dict) -> dict[str, DeclInfo]:
    """Build a name -> DeclInfo lookup from exported JSON."""
    index = {}
    for d in data["declarations"]:
        fields = None
        if "fields" in d and d["fields"] is not None:
            fields = [
                FieldInfo(name=f["name"], type=f["type"],
                          proj_name=f.get("projName", ""),
                          from_parent=f.get("fromParent", False))
                for f in d["fields"]
            ]

        ctors = None
        if "constructors" in d and d["constructors"] is not None:
            ctors = [
                CtorInfo(name=c["name"], type=c["type"])
                for c in d["constructors"]
            ]

        index[d["name"]] = DeclInfo(
            name=d["name"],
            kind=d["kind"],
            module=d["module"],
            is_private=d.get("is_private", False),
            type_signature=d["type_signature"],
            deps=d.get("deps", []),
            line=d.get("line"),
            fields=fields,
            constructors=ctors,
            value=d.get("value"),
            parents=d.get("parents"),
            has_sorry=d.get("has_sorry", False),
            docstring=d.get("docstring"),
        )
    return index


def dep_closure(index: dict[str, DeclInfo],
                     targets: list[str]) -> list[DeclInfo]:
    """Compute transitive dependency closure via BFS.

    Follows type + prop-erased value deps (proof deps are excluded).
    Gives the set of declarations needed to understand what every
    declaration means and computes.
    """
    visited: set[str] = set()
    queue = list(targets)
    order: list[DeclInfo] = []

    while queue:
        name = queue.pop(0)
        if name in visited:
            continue
        visited.add(name)
        if name not in index:
            continue
        decl = index[name]
        order.append(decl)
        for dep in decl.deps:
            if dep not in visited:
                queue.append(dep)

    return order


def display_name(decl: DeclInfo) -> str:
    """Get a readable display name for a declaration."""
    if decl.is_private:
        name = decl.name
        if name.startswith("_private."):
            parts = name.split(".")
            for i in range(len(parts) - 1, -1, -1):
                if parts[i].isdigit():
                    return ".".join(parts[i + 1:])
        return name
    return decl.name
