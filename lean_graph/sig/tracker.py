"""Core declaration tracking: index, BFS on type-level deps."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from ..common import _private_short_name, module_short
from ..graph import DeclarationGraph


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
    # v3 source-slice fields (audit-digest renderer). `source_text` is the verbatim
    # source of the declaration: signature + ` := by sorry` for proof-bearing decls,
    # whole decl verbatim otherwise. None when the exporter had no source range.
    source_text: Optional[str] = None
    # Byte spans (relative to source_text's UTF-8) of the outermost `by` proof
    # blocks, so a renderer can elide them with its own token (`sorry` for live
    # re-declared code, `⋯` for a comment). Empty/None when there's nothing to elide.
    byTactic_ranges: Optional[list] = None
    # Namespace open at the declaration's source position (e.g. "Quantum.Operators").
    decl_namespace: str = ""


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
            source_text=d.get("source_text"),
            byTactic_ranges=d.get("byTactic_ranges"),
            decl_namespace=d.get("decl_namespace", ""),
        )
    return index


class SigData:
    """Top-level export payload: index plus the v3 scope/import maps.

    Centralises access to the maps the audit-digest assembler needs so the CLI
    and the loopy wrapper read them the same way. All maps are keyed by full
    module name.
    """

    def __init__(self, data: dict):
        self.root_module: str = data.get("root_module", "")
        self.index: dict[str, DeclInfo] = build_index(data)
        self.project_modules: set[str] = set(data.get("project_modules", []))
        self.module_imports: dict[str, list[str]] = data.get("module_imports", {})
        self.module_opens: dict[str, list[str]] = data.get("module_opens", {})
        self.module_notations: dict[str, list[str]] = data.get("module_notations", {})
        self.module_variables: dict[str, list[str]] = data.get("module_variables", {})
        # All non-decl, non-structural, non-notation context commands per module,
        # verbatim in source order (opens + variables + attributes + set_options +
        # universes). Subsumes module_opens/module_variables for import_copies.
        self.module_context: dict[str, list[str]] = data.get("module_context", {})

    @property
    def has_source_text(self) -> bool:
        """True if the export carries the v3 source-slice fields."""
        return any(d.source_text is not None for d in self.index.values())


def dep_closure(index: dict[str, DeclInfo],
                     targets: list[str]) -> list[DeclInfo]:
    """Compute transitive dependency closure via BFS.

    Follows type + prop-erased value deps (proof deps are excluded).
    Gives the set of declarations needed to understand what every
    declaration means and computes.
    """
    graph = DeclarationGraph(index)
    return [
        index[name]
        for name in graph.closure_names(
            targets,
            "dependencies",
            include_roots=True,
        )
    ]


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
