"""Render a self-contained context file from declaration signatures."""

from __future__ import annotations

from ..common import module_short
from .tracker import DeclInfo, display_name


def _projection_names(decls: list[DeclInfo]) -> set[str]:
    """Collect all structure field projection names from a list of declarations.

    Used to filter out standalone projection declarations (abbrevs/theorems)
    that duplicate information already shown in the structure definition.
    """
    proj_names: set[str] = set()
    for d in decls:
        if d.fields:
            for f in d.fields:
                if f.proj_name:
                    proj_names.add(f.proj_name)
    return proj_names


# ===========================================================================
# v3 source-faithful audit-digest renderer
# ===========================================================================
#
# Instead of reconstructing pseudo-Lean from elaborated signatures, this path
# emits each declaration's VERBATIM source slice (carried in DeclInfo.source_text
# by the v3 exporter) and assembles a self-contained, compiling Lean module:
#   external imports -> per-module (namespace + opens + notations + decls) groups,
#   topologically ordered leaf-first so it type-checks.
#
# Python never parses Lean here: it only orders pre-sliced text blocks and reads
# the per-module scope strings the exporter provided.

import re
from collections import Counter, defaultdict, deque


def _decl_topo_order(decls: list[DeclInfo]) -> list[DeclInfo]:
    """Leaf-first topological order: a decl appears after every in-set dep.

    Deterministic tie-break by (module, line, name). Cycle members are appended
    in stable (module, line, name) order.
    """
    by_name = {d.name: d for d in decls}
    names = set(by_name)

    def key(n: str):
        d = by_name[n]
        return (d.module, d.line or 0, d.name)

    indeg = {n: 0 for n in names}
    dependents: dict[str, list[str]] = {n: [] for n in names}
    for d in decls:
        for dep in d.deps:
            if dep in names and dep != d.name:
                indeg[d.name] += 1
                dependents[dep].append(d.name)

    queue = deque(sorted((n for n in names if indeg[n] == 0), key=key))
    order: list[str] = []
    while queue:
        n = queue.popleft()
        order.append(n)
        ready = []
        for u in dependents[n]:
            indeg[u] -= 1
            if indeg[u] == 0:
                ready.append(u)
        for u in sorted(ready, key=key):
            queue.append(u)

    seen = set(order)
    for n in sorted(names - seen, key=key):
        order.append(n)
    return [by_name[n] for n in order]


def _module_topo_order(members: list[DeclInfo], index: dict[str, DeclInfo]) -> list[str]:
    """Leaf-first topological order of the modules spanned by ``members``."""
    modset = {d.module for d in members}
    mdeps: dict[str, set[str]] = {m: set() for m in modset}
    for d in members:
        for dep in d.deps:
            dd = index.get(dep)
            if dd is not None and dd.module in modset and dd.module != d.module:
                mdeps[d.module].add(dd.module)

    indeg = {m: len(mdeps[m]) for m in modset}
    dependents: dict[str, list[str]] = {m: [] for m in modset}
    for m, deps in mdeps.items():
        for dm in deps:
            dependents[dm].append(m)

    queue = deque(sorted(m for m in modset if indeg[m] == 0))
    order: list[str] = []
    while queue:
        m = queue.popleft()
        order.append(m)
        ready = []
        for u in dependents[m]:
            indeg[u] -= 1
            if indeg[u] == 0:
                ready.append(u)
        for u in sorted(ready):
            queue.append(u)

    for m in sorted(modset - set(order)):
        order.append(m)
    return order


def _external_imports(
    closure_modules: set[str],
    module_imports: dict[str, list[str]],
    project_modules: set[str],
) -> list[str]:
    """External (non-project) modules to ``import``.

    Walks the project-local import graph transitively from the closure's
    modules, harvesting every external direct-import along the way. The walk
    must be transitive because the digest re-declares project modules instead of
    importing them, so an external symbol reached via a project import would
    otherwise be lost.
    """
    visited: set[str] = set()
    queue = deque(m for m in closure_modules if m in project_modules)
    visited.update(queue)
    external: set[str] = set()
    while queue:
        m = queue.popleft()
        for imp in module_imports.get(m, []):
            if imp in project_modules:
                if imp not in visited:
                    visited.add(imp)
                    queue.append(imp)
            else:
                external.add(imp)
    return sorted(external)


def _primary_namespace(decls: list[DeclInfo]) -> tuple[str, bool]:
    """Return (namespace, is_uniform) for a module's decls."""
    nss = [d.decl_namespace for d in decls if d.decl_namespace]
    if not nss:
        return "", True
    counts = Counter(nss)
    return counts.most_common(1)[0][0], len(counts) == 1


def _apply_elision(decl: DeclInfo, token: str) -> str:
    """The decl's source slice with its `by` proof blocks replaced by ``token``.

    Byte-splices (``byTactic_ranges`` are UTF-8 byte offsets into ``source_text``)
    so the heavily-unicode QI source is handled correctly. With no ranges (older
    caches, or a proof-free decl) it returns the slice unchanged. Live-code modes
    pass ``sorry``; the print-comment passes ``⋯`` (a literal ``sorry`` in a def
    term would read as a dishonest stub).
    """
    src = decl.source_text or ""
    ranges = decl.byTactic_ranges or []
    if not ranges:
        return src
    b = src.encode("utf-8")
    tok = token.encode("utf-8")
    for s, e in sorted(ranges, reverse=True):
        if 0 <= s <= e <= len(b):
            b = b[:s] + tok + b[e:]
    return b.decode("utf-8", errors="replace")


def _render_decl_source(decl: DeclInfo) -> str:
    """Verbatim source slice (proofs → `sorry` so re-declared code compiles), or a
    placeholder comment when none was exported (the exporter always emits a slice
    for a primary declaration, so this only fires for the rare slice-less decl)."""
    if decl.source_text:
        return _apply_elision(decl, "sorry")
    return f"-- (no source slice available for {decl.kind} {display_name(decl)})"


def _preamble_options() -> list[str]:
    """Top-level options the digest needs to be robust.

    A re-declared module emits its whole notation block, but some notations
    point at decls outside the closure (so their target isn't declared here).
    Disabling the quotation precheck lets those notations be declared anyway;
    they are harmless unless actually used.
    """
    return ["set_option quotPrecheck false",
            "set_option linter.all false"]


def _digest_banner(targets, members, root_module, header, subtitle) -> list[str]:
    bar = "-- " + "=" * 70
    target_names = {t.name for t in targets}
    nont = [d for d in members if d.name not in target_names]
    n_mods = len({d.module for d in members})
    lines = [bar, "-- AUDIT DIGEST" + (f" — {header}" if header else ""),
             f"-- {subtitle}", bar, "-- Targets under audit:"]
    for t in targets:
        lines.append(f"--   ◾ {t.name}  ({module_short(t.module, root_module)}:{t.line or '?'})")
    lines.append(f"-- Dependency closure: {len(nont)} dependencies + target, "
                 f"across {n_mods} modules (leaf-first below).")
    return lines


def _ns_prefixes(ns: str) -> set[str]:
    """All dotted prefixes of a namespace ("A.B.C" -> {A, A.B, A.B.C})."""
    if not ns:
        return set()
    parts = ns.split(".")
    return {".".join(parts[:i]) for i in range(1, len(parts) + 1)}


def _project_namespaces(project_modules: set[str], root_module: str) -> set[str]:
    """Approximate set of project-local namespaces from module paths.

    A namespace is project-local iff it is a dotted prefix of some project
    module name with the root module stripped (QI convention: module
    ``Root.A.B.C`` lives in namespace ``A.B`` / ``A.B.C``).
    """
    out: set[str] = set()
    prefix = root_module + "." if root_module else ""
    for m in project_modules:
        stripped = m[len(prefix):] if prefix and m.startswith(prefix) else m
        out |= _ns_prefixes(stripped)
    return out


_OPEN_RE = re.compile(r"^\s*open\s+(?:scoped\s+)?(.*)", re.S)


def _open_referenced_namespaces(open_line: str) -> list[str]:
    """Lenient extraction of the namespace names an ``open`` command references.

    Handles ``open A B``, ``open scoped A``, ``open A (x y)``, ``open A renaming …``.
    Only used to decide whether an open targets an absent project namespace, so
    over- or under-matching just makes the filter more or less conservative.
    """
    m = _OPEN_RE.match(open_line)
    if not m:
        return []
    rest = m.group(1)
    for stop in ("(", " renaming", " hiding"):
        idx = rest.find(stop)
        if idx != -1:
            rest = rest[:idx]
    return [t for t in rest.replace("\n", " ").split() if t and (t[0].isalpha() or t[0] == "_")]


_OPEN_SPLIT_RE = re.compile(r"^(\s*open\s+)(scoped\s+)?(.*)$", re.S)


def _filter_opens(opens: list[str], project_ns: set[str], populated_ns: set[str]) -> list[str]:
    """Drop opens of project namespaces absent from the digest, WITHOUT losing the
    rest of a multi-namespace command.

    ``open A B C`` where ``B`` has no re-declared decls would raise ``unknown
    namespace``; but dropping the whole command also loses ``A``/``C``. So a plain
    multi-namespace open is split and filtered per namespace (Mathlib namespaces,
    not in ``project_ns``, are always kept). Selector / ``renaming`` / ``hiding``
    forms can't be split, so they're kept-or-dropped whole.
    """
    def absent(r: str) -> bool:
        return r in project_ns and r not in populated_ns

    kept = []
    for o in opens:
        if any(tok in o for tok in ("(", " renaming", " hiding")):
            if not any(absent(r) for r in _open_referenced_namespaces(o)):
                kept.append(o)
            continue
        m = _OPEN_SPLIT_RE.match(o)
        if not m:
            kept.append(o)
            continue
        head, scoped, body = m.group(1), m.group(2) or "", m.group(3)
        names = [n for n in body.replace("\n", " ").split() if not absent(n)]
        if names:
            kept.append(f"{head}{scoped}{' '.join(names)}")
    return kept


def _emit_module_group(
    lines: list[str],
    mod: str,
    decls: list[DeclInfo],
    target_names: set[str],
    root_module: str,
    module_opens: dict[str, list[str]],
    module_notations: dict[str, list[str]],
    module_variables: dict[str, list[str]],
    project_ns: set[str] | None = None,
    populated_ns: set[str] | None = None,
) -> None:
    """Append one ``namespace … end`` group for a module's decls."""
    decls = _decl_topo_order(decls)
    ns, uniform = _primary_namespace(decls)
    mshort = module_short(mod, root_module)
    lines.append(f"-- {'═' * 4} from {mshort} {'═' * 4}")
    if not uniform:
        lines.append(f"-- NOTE: module spans multiple namespaces; grouped under `{ns}` "
                     f"(some decls may need their own namespace).")
    if ns:
        lines.append(f"namespace {ns}")
    opens = module_opens.get(mod, [])
    if project_ns is not None and populated_ns is not None:
        opens = _filter_opens(opens, project_ns, populated_ns)
    for opn in opens:
        lines.append(opn)
    for var in module_variables.get(mod, []):
        lines.append(var)
    for nota in module_notations.get(mod, []):
        lines.append(nota)
    lines.append("")
    for d in decls:
        tag = "◾ TARGET" if d.name in target_names else "◾"
        lines.append(f"-- {tag} {display_name(d)} ({mshort}:{d.line or '?'})")
        lines.append(_render_decl_source(d))
        lines.append("")
    if ns:
        lines.append(f"end {ns}")
    lines.append("")


def render_digest(
    targets: list[DeclInfo],
    closure: list[DeclInfo],
    index: dict[str, DeclInfo],
    *,
    root_module: str = "",
    module_imports: dict[str, list[str]] | None = None,
    module_opens: dict[str, list[str]] | None = None,
    module_notations: dict[str, list[str]] | None = None,
    module_variables: dict[str, list[str]] | None = None,
    module_context: dict[str, list[str]] | None = None,
    project_modules: set[str] | None = None,
    mode: str = "print",
    header: str = "",
    show_source: bool = True,
) -> str:
    """Assemble a compiling, source-faithful audit digest.

    ``closure`` includes the targets (roots). ``mode``:
      - ``print`` (default): import the real closure modules and show, per decl, a
        dependency tree, the docstring, the verbatim source slice (authored), and
        `#check`/`#print` of the imported decl (the elaborator's ground truth, for
        source-vs-elaborated comparison). Needs the library built. ``show_source``
        toggles the slice.
      - ``self_contained``: a self-contained mini-library — ``import Mathlib`` only,
        with the closure's notation + decls re-declared verbatim in their real
        namespaces, leaf-first, proofs sorried. Compiles standalone (no library
        needed); the notation elaborates as in the library.
      - ``connected``: one ``Audit`` namespace; the closure re-declared leaf-first
        so copies reference each other (target last), real modules imported. Breaks
        on project notation (expands to real decls → real/copy mismatch).
      - ``import_copies``: each decl a verbatim copy isolated in its own namespace,
        resolving to the real imports (target first). Robust but each decl stands
        alone (not wired to the others).
      - ``comparator``: import the real closure modules; restate targets only.
      - ``self_contained_legacy``: old whole-block re-declaration (fragile).
    """
    module_imports = module_imports or {}
    module_opens = module_opens or {}
    module_notations = module_notations or {}
    module_variables = module_variables or {}
    module_context = module_context or {}
    project_modules = project_modules or set()

    target_names = {t.name for t in targets}
    by_name = {d.name: d for d in closure}

    # Drop standalone projection decls already shown inside their structure slice.
    proj_names = _projection_names(list(closure))
    members = [d for d in closure if d.name not in proj_names or d.name in target_names]

    if mode == "print":
        return _render_print(targets, members, index, root_module=root_module,
                             header=header, show_source=show_source)

    if mode == "self_contained":
        return _render_self_contained(
            targets, members, index, root_module=root_module,
            module_imports=module_imports, module_opens=module_opens,
            module_notations=module_notations, module_variables=module_variables,
            module_context=module_context, project_modules=project_modules, header=header,
        )

    if mode == "connected":
        return _render_connected(
            targets, members, root_module=root_module, module_opens=module_opens,
            module_variables=module_variables, module_context=module_context,
            project_modules=project_modules, header=header,
        )

    if mode == "import_copies":
        return _render_import_copies(
            targets, members, root_module=root_module, module_opens=module_opens,
            module_variables=module_variables, module_context=module_context,
            project_modules=project_modules, header=header,
        )

    if mode == "comparator":
        return _render_comparator(
            targets, members, by_name, root_module, module_imports,
            module_opens, module_notations, module_variables, project_modules, header,
        )

    # Legacy self-contained (emits a module's whole notation block; fragile on
    # notation-heavy closures). Kept for comparison via mode="self_contained_legacy".
    closure_modules = {d.module for d in members}
    ext_imports = _external_imports(closure_modules, module_imports, project_modules)

    lines = _digest_banner(targets, members, root_module, header,
                           "source-faithful, self-contained LEGACY (compiles standalone)")
    lines.append("")
    for imp in ext_imports:
        lines.append(f"import {imp}")
    lines.append("")
    lines.extend(_preamble_options())
    lines.append("")
    # A digest is never run, so make every re-declared def noncomputable. This
    # avoids IR-compile failures from defs that (in source) lived under a
    # `noncomputable section` — context the per-decl slice doesn't carry.
    lines.append("noncomputable section")
    lines.append("")

    by_module: dict[str, list[DeclInfo]] = {}
    for d in members:
        by_module.setdefault(d.module, []).append(d)

    project_ns = _project_namespaces(project_modules, root_module)
    populated_ns: set[str] = set()
    for d in members:
        populated_ns |= _ns_prefixes(d.decl_namespace)

    for mod in _module_topo_order(members, index):
        _emit_module_group(lines, mod, by_module[mod], target_names, root_module,
                           module_opens, module_notations, module_variables,
                           project_ns, populated_ns)

    lines.append("end")  # close `noncomputable section`
    return "\n".join(lines)


def _collect_context(members, module_opens, module_variables, module_context):
    """Union (dedup, first-seen order) of every decl's context, split into
    `open` lines and the rest (variable/attribute/set_option)."""
    opens, oseen, other, cseen = [], set(), [], set()
    for d in members:
        raw = module_context.get(d.module)
        if raw is None:
            raw = module_opens.get(d.module, []) + module_variables.get(d.module, [])
        for c in ([f"open {d.decl_namespace}"] if d.decl_namespace else []) + raw:
            key = " ".join(c.split())
            if c.lstrip().startswith("open "):
                if key not in oseen:
                    oseen.add(key)
                    opens.append(c)
            elif key not in cseen:
                cseen.add(key)
                other.append(c)
    return opens, other


def _render_connected(
    targets: list[DeclInfo],
    members: list[DeclInfo],
    *,
    root_module: str = "",
    module_opens: dict[str, list[str]] | None = None,
    module_variables: dict[str, list[str]] | None = None,
    module_context: dict[str, list[str]] | None = None,
    project_modules: set[str] | None = None,
    header: str = "",
    namespace: str = "Audit",
) -> str:
    """Connected "mini-replica" digest.

    One namespace; the closure re-declared LEAF-FIRST so each copy references the
    EARLIER copies (current-namespace resolution shadows the opened real imports),
    with the target last. The real modules are imported only for Mathlib + notation.
    Compiling it therefore checks that the shown definitions actually chain together
    to state the target — a real check, unlike import-copies' per-decl isolation.

    Caveat: a body that uses a project notation (`⊗`, `|0⟩`, `Y`, …) won't compile,
    because notations expand HYGIENICALLY to the real decls, not the copies, so the
    body mixes real + copy types. That clears once the project's notations are
    removed; until then, `mode="import_copies"` is the compiling fallback.
    """
    module_opens = module_opens or {}
    module_variables = module_variables or {}
    module_context = module_context or {}
    project_modules = project_modules or set()
    target_names = {t.name for t in targets}
    closure_modules = sorted({d.module for d in members})

    opens, other_ctx = _collect_context(members, module_opens, module_variables, module_context)

    lines = _digest_banner(targets, members, root_module, header,
                           "connected: one namespace, decls wired to each other, "
                           "leaf-first (target is LAST)")
    lines.append("")
    for m in closure_modules:
        lines.append(f"import {m}")
    lines.append("")
    lines.extend(_preamble_options())
    lines.append("")
    lines.append("noncomputable section")
    lines.append(f"namespace {namespace}")
    lines.extend(opens)
    lines.extend(other_ctx)
    lines.append("")

    for d in _decl_topo_order(members):   # leaf-first → dependencies first, target last
        mshort = module_short(d.module, root_module)
        tag = "◾ TARGET" if d.name in target_names else "◾"
        lines.append(f"-- {tag} {display_name(d)} ({mshort}:{d.line or '?'})")
        if d.source_text:
            lines.append(d.source_text)
        else:
            lines.append(f"-- (no source slice available for {d.kind} {d.name})")
        lines.append("")

    lines.append(f"end {namespace}")
    lines.append("end")  # close `noncomputable section`
    return "\n".join(lines)


def _render_import_copies(
    targets: list[DeclInfo],
    members: list[DeclInfo],
    *,
    root_module: str = "",
    module_opens: dict[str, list[str]] | None = None,
    module_variables: dict[str, list[str]] | None = None,
    module_context: dict[str, list[str]] | None = None,
    project_modules: set[str] | None = None,
    header: str = "",
) -> str:
    """Robust, compile-first digest.

    `import` the real modules that define the closure (this also pulls their
    transitive Mathlib + project deps, so every definition, notation, and custom
    elaborator exists exactly as the author wrote it). Then show each closure
    decl as a verbatim source copy, each isolated in its own `namespace _Audit.dN`
    that opens only the REAL namespaces. Because the `_Audit.*` namespaces are
    never opened, copies never reference each other — every identifier in a copy
    resolves to the real imported decl, so nothing needs reconstructing.
    """
    module_opens = module_opens or {}
    module_variables = module_variables or {}
    module_context = module_context or {}
    project_modules = project_modules or set()
    target_names = {t.name for t in targets}

    closure_modules = sorted({d.module for d in members})
    # No open-filtering here: a module can only `open` namespaces it `import`s, and
    # we `import` every closure module, so every namespace its opens reference is
    # transitively imported and available. Emitting opens verbatim is both correct
    # and necessary — a source `open A B C` may mix namespaces, and dropping the
    # whole command (filter) would lose the needed ones.

    # Target(s) first (read the statement under audit), then deps by (module, line).
    ordered = list(targets) + sorted((d for d in members if d.name not in target_names),
                                     key=lambda d: (d.module, d.line or 0, d.name))

    def _ctx_for(d: DeclInfo) -> list[str]:
        """A decl's context lines: `open <its namespace>` + its module_context,
        deduped (a source file often repeats the same opens across sections)."""
        raw = module_context.get(d.module)
        if raw is None:
            raw = module_opens.get(d.module, []) + module_variables.get(d.module, [])
        out, seen = [], set()
        for c in ([f"open {d.decl_namespace}"] if d.decl_namespace else []) + raw:
            key = " ".join(c.split())
            if key not in seen:
                seen.add(key)
                out.append(c)
        return out

    # Split context into OPEN lines and the rest. `open`s are HOISTED to the top
    # (a top-level open reaches into every namespace below, verified), so the union
    # is emitted once instead of repeated per block. Non-open context
    # (`variable`/`attribute`/`set_option`) stays per-decl — at top level it would
    # over-apply to unrelated decls.
    hoisted_opens, hseen = [], set()
    per_decl_ctx: dict[str, list[str]] = {}
    for d in ordered:
        rest = []
        for c in _ctx_for(d):
            if c.lstrip().startswith("open "):
                key = " ".join(c.split())
                if key not in hseen:
                    hseen.add(key)
                    hoisted_opens.append(c)
            else:
                rest.append(c)
        per_decl_ctx[d.name] = rest

    lines = _digest_banner(targets, members, root_module, header,
                           "import-copies: real deps imported; decls shown as verbatim copies")
    lines.append("")
    for m in closure_modules:
        lines.append(f"import {m}")
    lines.append("")
    # Guards: a re-emitted `open scoped` may pull notation whose target is outside
    # the closure (quotPrecheck); linters are noise on copied code; copied data
    # values may need noncomputable to avoid IR-codegen checks.
    lines.extend(_preamble_options())
    lines.append("")
    lines.extend(hoisted_opens)         # shared opens, once, at the top
    lines.append("")
    lines.append("noncomputable section")
    lines.append("")

    for i, d in enumerate(ordered):
        mshort = module_short(d.module, root_module)
        tag = "◾ TARGET" if d.name in target_names else "◾"
        lines.append(f"-- {tag} {display_name(d)} ({mshort}:{d.line or '?'})")
        if not d.source_text:
            lines.append(f"-- (no source slice available for {d.kind} {d.name})")
            lines.append("")
            continue
        lines.append(f"namespace _Audit.d{i}")
        lines.extend(per_decl_ctx[d.name])
        lines.append(d.source_text)
        lines.append(f"end _Audit.d{i}")
        lines.append("")

    lines.append("end")  # close `noncomputable section`
    return "\n".join(lines)


def _render_comparator(
    targets, members, by_name, root_module, module_imports,
    module_opens, module_notations, module_variables, project_modules, header,
) -> str:
    target_names = {t.name for t in targets}
    target_modules = {t.module for t in targets}
    nont = [d for d in members if d.name not in target_names]

    import_mods = sorted({d.module for d in nont} - target_modules)
    ext: set[str] = set()
    for tm in target_modules:
        for imp in module_imports.get(tm, []):
            if imp not in project_modules:
                ext.add(imp)
    # Non-target deps sharing a target module can't be imported (would drag the
    # target's real proof + clash); re-declare them inline.
    inline = [d for d in nont if d.module in target_modules]

    lines = _digest_banner(targets, members, root_module, header,
                           "comparator challenge (imports real deps; targets sorried)")
    lines.append("")
    for imp in sorted(ext):
        lines.append(f"import {imp}")
    for m in import_mods:
        lines.append(f"import {m}")
    lines.append("")
    lines.extend(_preamble_options())
    lines.append("")

    if inline:
        lines.append("-- Same-module dependencies (cannot be imported without the target proof):")
        inline_by_mod: dict[str, list[DeclInfo]] = {}
        for d in inline:
            inline_by_mod.setdefault(d.module, []).append(d)
        for mod in _module_topo_order(inline, by_name):
            _emit_module_group(lines, mod, inline_by_mod[mod], set(), root_module,
                               module_opens, module_notations, module_variables)

    lines.append("-- Targets (challenge statements):")
    for t in targets:
        ns = t.decl_namespace
        if ns:
            lines.append(f"namespace {ns}")
        for opn in module_opens.get(t.module, []):
            lines.append(opn)
        for nota in module_notations.get(t.module, []):
            lines.append(nota)
        lines.append(_render_decl_source(t))
        if ns:
            lines.append(f"end {ns}")
        lines.append("")

    return "\n".join(lines)


# ===========================================================================
# self-contained mini-library (DEFAULT)
# ===========================================================================
#
# The chosen audit artifact (de-risk-validated 2026-06-17): a single file that
# `import Mathlib` ONLY — no project imports, so nothing to clash with — and
# RE-DECLARES the closure's notation + decls verbatim in their REAL namespaces,
# leaf-first, proofs sorried. Because nothing project-level is imported there is
# no real-vs-copy split: notation expands to the re-declared decls and elaborates
# exactly as in the library.
#
# The two non-trivial steps the recipe requires:
#   (1) Notation SELECTION — include a notation command only if it is actually
#       used (its keyword atoms appear in some shown decl's source) or its RHS is
#       a shown decl. Blindly emitting a module's whole notation block over-
#       captures (the Gates X/Z/H block, the NormKet block) and drags heavy,
#       unused helper sub-closures.
#   (2) Notation-closure DELTA — a used notation's RHS references helper defs
#       (e.g. `|x⟩ => ToKet.toKet x`) that the *type*-level closure doesn't carry;
#       pull them in, plus saturate the instances those helpers need to elaborate.

from .tracker import dep_closure

_QUOTED_RE = re.compile(r'"((?:[^"\\]|\\.)*)"')
_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")
# Body-scan tokenizer for recovering proof-helper refs from an emitted decl body.
# Unlike `_IDENT_RE` (ASCII-only, for notation RHS), this is Unicode-aware: Lean
# identifiers routinely start with a non-ASCII letter (`ρ`, `σ`, `τ`, …) or embed
# one (`hεcor0`). If the receiver of a dot-call is dropped by an ASCII-only match,
# `ρ.method` collapses to a bare `method` that can no longer be receiver-type
# disambiguated and misresolves via the global suffix map (this is how a
# `LinearMap.comp` call pulled in the unrelated `IsCPTNI.comp`). `[^\W\d]` starts
# on any Unicode word char that is not a digit; `re` is Unicode-aware by default.
_BODY_IDENT_RE = re.compile(r"[^\W\d][\w.']*")
# Lean syntax words that show up in a notation RHS / macro expansion but are never
# project decls — skip them when recovering rhs idents from raw text.
_RHS_NOISE = {
    "fun", "match", "with", "if", "then", "else", "let", "do", "by", "term",
    "Type", "Prop", "Sort", "true", "false",
}


def _extract_tokens(text: str) -> list[str]:
    """Literal string atoms a notation introduces (regex fallback when the
    exporter didn't supply them). Includes atoms inside a `set_option … in` wrap."""
    return _QUOTED_RE.findall(text)


def _extract_rhs_idents(text: str) -> list[str]:
    """Identifiers appearing after the first `=>` (the notation RHS / macro
    expansion). A best-effort fallback; the v4 exporter supplies precise ones."""
    idx = text.find("=>")
    rhs = text[idx + 2:] if idx != -1 else ""
    return [t for t in _IDENT_RE.findall(rhs) if t not in _RHS_NOISE]


def _notation_meta(entry) -> dict:
    """Normalize a `module_notations` entry into {text, line, tokens, rhs_idents}.

    Accepts both the v4 object form ({text, line, kind, tokens, rhs_idents}) and
    the older bare-string form, recovering any missing field from the text so the
    renderer works against any cache.
    """
    if isinstance(entry, dict):
        text = entry.get("text", "")
        line = entry.get("line", 0) or 0
        tokens = entry.get("tokens")
        rhs = entry.get("rhs_idents")
    else:
        text, line, tokens, rhs = str(entry), 0, None, None
    if tokens is None:
        tokens = _extract_tokens(text)
    if rhs is None:
        rhs = _extract_rhs_idents(text)
    return {"text": text, "line": line, "tokens": tokens, "rhs_idents": rhs}


def _strip_comments(src: str) -> str:
    """Remove Lean block comments ``/- … -/`` (incl. docstrings ``/-- … -/``,
    nested) and line comments ``-- …``. Used only to build the token-detection
    blob, so prose like ``A† = A`` in a docstring can't falsely select the ``†``
    notation. The emitted decls keep their docstrings."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif two == "--":
            j = src.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def _token_present(token: str, blob: str) -> bool:
    """Is a notation's keyword atom actually used somewhere in the shown sources?

    Alphanumeric atoms (`X`, `Y`, `H`, `S_gate`) are matched with identifier
    boundaries so they don't fire on substrings of unrelated names; symbolic atoms
    (`|0⟩`, `⊗`, `‖`) are matched as plain substrings.
    """
    t = token.strip()
    if not t:
        return True
    if t[0].isalnum() or t[0] == "_":
        return re.search(r"(?<![A-Za-z0-9_'])" + re.escape(t) + r"(?![A-Za-z0-9_'])", blob) is not None
    return t in blob


_IDENT_WORD_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def _atom_used_as_binder(atom: str, blob: str) -> bool:
    """True if an identifier-word notation atom (`X`, `Z`, `H`, …) appears in a
    BINDER position in the shown sources.

    In the flattened mini-library the import isolation that lets a single-word
    notation token coexist with a same-named binder in the real library is gone:
    re-declaring `notation "X" => pauliX` turns `X` into a keyword token, which
    then breaks every later `(X : …)`, `∃ X : …, …`, or structure param `(S X Z :
    Type*)`. Only identifier-word atoms can collide this way; symbolic atoms
    (`⊗`, `|0⟩`, `†`) never can, so they short-circuit to False.

    Detects the two binder shapes that occur in a signature: a parenthesized/
    bracketed binder group `([{⦃ … X … :` (before any closing delim or `:`), and a
    `∀`/`∃`/`λ`/`fun` binder `… X … ,` / `… X … =>`.
    """
    if not _IDENT_WORD_RE.match(atom):
        return False
    esc = re.escape(atom)
    grp = r"[A-Za-z0-9_'⟨⟩]+"
    # `(… X … :` inside a paren/brace/instance binder group, before any `)`/`:`.
    paren = re.compile(r"[\[({⦃][^)}\]:]*?(?<![A-Za-z0-9_'])" + esc
                       + r"(?![A-Za-z0-9_'])[^)}\]:]*?:")
    # `∀`/`∃`/`λ`/`Σ`/`Π`/`fun` … X … `,`/`=>`.
    quant = re.compile(r"(?:[∀∃λΣΠ]|\bfun\b)\s*(?:" + grp + r"\s+)*" + esc
                       + r"\b[^,=]*(?:,|=>)")
    return bool(paren.search(blob) or quant.search(blob))


def _receiver_type_head(recv: str, body: str) -> str | None:
    """Short type head of the local variable `recv` from its binder in `body`.

    Finds a binder group `([{⦃ … recv … : TypeHead …` and returns the last segment
    of `TypeHead` (`(atk : GeneralAttackLinear 4 n)` -> ``"GeneralAttackLinear"``).
    Used to resolve a dot-notation call `recv.method` to the single overload on
    that type, without pulling every same-named overload (which would cascade)."""
    m = re.search(r"[(\[{⦃][^:)}\]]*?(?<![A-Za-z0-9_'])" + re.escape(recv)
                  + r"(?![A-Za-z0-9_'])[^:)}\]]*?:\s*@?([A-Za-z_][A-Za-z0-9_.']*)", body)
    return m.group(1).rsplit(".", 1)[-1] if m else None


def _resolve_idents(raw_idents, index: dict[str, DeclInfo]) -> set[str]:
    """Map raw (unqualified or partially-qualified) idents to project FQNs by
    suffix match against the decl index. Mathlib idents simply don't match."""
    out: set[str] = set()
    keys = list(index.keys())
    for raw in raw_idents:
        if raw in index:
            out.add(raw)
            continue
        suf = "." + raw
        for k in keys:
            if k.endswith(suf):
                out.add(k)
    return out


# Non-term syntax categories: a `: tactic` / `: command` / … notation only ever
# appears in proofs or top-level commands, never in a statement's type, so it is
# never needed by a statement audit (and its body's simp-set would otherwise
# false-trigger an rhs hit on member lemmas).
_NONTERM_CAT_RE = re.compile(r":\s*(tactic|command|conv|doElem|attr|prec|prio|level|stx)\b")


def _select_notations(
    module_notations: dict[str, list],
    members: list[DeclInfo],
    index: dict[str, DeclInfo],
) -> dict[str, list[dict]]:
    """{module: [meta,…]} of notations worth re-declaring for this closure.

    A notation is included iff every keyword atom it introduces appears in some
    member's source (it is genuinely used), OR its RHS resolves to a member. The
    conjunction over atoms is what excludes `‖…⟩` (its distinctive `‖` is absent)
    and `notation "X"` (no bare `X` token) while keeping `|0⟩`, `⊗`, `Y`.
    """
    member_names = {d.name for d in members}
    blob = "\n".join(_strip_comments(d.source_text or "") for d in members)
    selected: dict[str, list[dict]] = {}
    for mod, entries in module_notations.items():
        for entry in entries or []:
            meta = _notation_meta(entry)
            if _NONTERM_CAT_RE.search(meta["text"]):
                continue
            atoms = [t for t in meta["tokens"] if t.strip()]
            # A single-word notation token that also appears as a BINDER in the
            # shown sources would shadow that binder once re-declared and break
            # parsing in the flattened file (the Gates `X`/`Z` block over the
            # `(X : …)` binders in `diamondNorm`/`mapTensorId`/`QuantumHashFamily`).
            # Drop it — it is sugar for a named def that is itself re-declared, and
            # a signature audit never needs the letter-notation.
            if any(_atom_used_as_binder(t, blob) for t in atoms):
                continue
            tokens_ok = bool(atoms) and all(_token_present(t, blob) for t in atoms)
            rhs_hit = bool(_resolve_idents(meta["rhs_idents"], index) & member_names)
            if tokens_ok or rhs_hit:
                selected.setdefault(mod, []).append(meta)
    return selected


_THEOREM_KINDS = {"theorem", "lemma", "example"}


def _rhs_key(meta: dict) -> str:
    """A notation's expansion, normalized — used with its token-set to detect
    DUPLICATE notations (same token + same RHS, e.g. the global and five `local`
    `postfix † => Matrix.conjTranspose`) while preserving genuine type-overloads
    (`⊗` for Ket/Bra/Op all share the token but differ in RHS)."""
    t = meta["text"]
    i = t.rfind("=>")
    return " ".join((t[i + 2:] if i != -1 else t).split())


def _dedup_notations(selected: dict[str, list[dict]]) -> dict[str, list[dict]]:
    """Keep one notation per (token-set, RHS) — drops re-declared duplicates that
    make a use site ``Ambiguous term``, preferring a non-``local`` declaration."""
    best: dict[tuple, tuple] = {}
    for mod, metas in selected.items():
        for meta in metas:
            key = (frozenset(t.strip() for t in meta["tokens"] if t.strip()), _rhs_key(meta))
            is_local = meta["text"].lstrip().startswith("local")
            if key not in best or (best[key][2] and not is_local):
                best[key] = (mod, meta, is_local)
    out: dict[str, list[dict]] = {}
    for mod, meta, _ in best.values():
        out.setdefault(mod, []).append(meta)
    return out


def _expand_and_select(
    initial: list[DeclInfo],
    index: dict[str, DeclInfo],
    module_notations: dict[str, list],
) -> tuple[list[DeclInfo], dict[str, list[dict]]]:
    """Grow the type-level closure to a NOTATION closure and return the final
    members plus the notations selected for them.

    Fixpoint: select used notations → pull the helper defs/classes their RHS names
    → close those under type-deps → pull the instances of those helper CLASSES
    (a notation like ``|x⟩ => ToKet.toKet x`` needs a ``ToKet`` instance to
    elaborate, and instances aren't referenced syntactically). Repeat to fixpoint.

    Two hard rules keep this from ballooning (cf. the de-risk, which added 9 decls
    and zero theorems): (a) NEVER pull a theorem — a statement's type-level closure
    is theorem-free, and a pulled theorem's *statement* can drag in unrelated
    notation (`†`, tactic macros) and its proof helpers; (b) only saturate
    instances OF the helper classes, not every instance whose deps happen to be
    satisfiable (that cascades through the whole algebra hierarchy).
    """
    members: dict[str, DeclInfo] = {d.name: d for d in initial}

    # Suffix index for fast resolution of source-text idents (incl. the last
    # segment of a dotted `recv.method` reference).
    suffix_map: dict[str, set[str]] = defaultdict(set)
    for fqn in index:
        parts = fqn.split(".")
        for i in range(len(parts)):
            suffix_map[".".join(parts[i:])].add(fqn)

    def satisfied(dep: str) -> bool:
        # A dep is "available" if shown, external (Mathlib), or an auto-generated
        # projection/constructor (no source slice — it arrives with its structure).
        if dep in members:
            return True
        d = index.get(dep)
        return d is None or not d.source_text

    for _ in range(64):
        added = False
        selected = _select_notations(module_notations, list(members.values()), index)
        rhs_all = [r for metas in selected.values() for m in metas for r in m["rhs_idents"]]
        resolved = _resolve_idents(rhs_all, index)

        # Helper defs/classes named in notation RHSs, plus the class behind a
        # class-projection like `ToKet.toKet` -> `ToKet`.
        helper_classes: set[str] = set()
        for n in resolved:
            d = index.get(n)
            if d is None:
                continue
            if d.kind == "class":
                helper_classes.add(n)
            parent = n.rsplit(".", 1)[0]
            pd = index.get(parent)
            if pd is not None and pd.kind == "class":
                helper_classes.add(parent)
            if n not in members:
                members[n] = d
                added = True
        for c in helper_classes:
            if c not in members:
                members[c] = index[c]
                added = True

        # FULL deps of every shown (non-theorem) body. A def/structure/instance is
        # shown verbatim, so everything its body references must be present — both
        # data defs and the proof-field lemmas (e.g. a `DensityOp` instance's
        # `pos_semidef` proof). Theorems are skipped here: their slice is sorried,
        # so we never need their proof deps (only their statement deps, via the
        # type-level closure below) — which is what stops a theorem target from
        # dragging in its entire proof tree.
        for d in list(members.values()):
            if d.kind in _THEOREM_KINDS:
                continue
            for dep in d.deps:
                if dep in index and dep not in members:
                    members[dep] = index[dep]
                    added = True

        # Source-text references not tracked in `deps`. A shown non-theorem body is
        # emitted VERBATIM (proofs `by`-elided to `sorry`), so every identifier that
        # survives elision must be re-declared or it is an unknown identifier. Two
        # kinds are prop-erased from a def's recorded `deps` and so are invisible to
        # the pass above: (a) TERM-mode proof fields, e.g.
        # `map_add' := (mapTensorId_isLinearMap Φ).map_add`, and (b) dot-notation
        # methods, e.g. `atk.neZeroEveDim`. Recover them from the EMITTED text.
        #
        # Resolve each source ident to project decl(s) and pull it (emitted
        # sorried). Bloat guards: a plain unqualified ident is pulled only when it
        # resolves UNIQUELY (`mapTensorId_isLinearMap`, `bb84BaseOutputDim_neZero`);
        # a dotted `recv.method` keeps the overload(s) whose receiver TYPE is already
        # shown (`neZeroEveDim` -> the `GeneralAttack{,Linear}` overloads, not
        # `BobEveAttackLinear`), else falls back to the old ≤3-unambiguous rule; a
        # plain AMBIGUOUS ident (`toOp`, `trace`, `mk`) is left to dot-notation on
        # its already-present receiver type.
        # Only PROOF-producing helpers (theorem/lemma) are recovered here: those are
        # exactly the refs prop-erased from `deps` (a term-mode proof field or a
        # `haveI := recv.method`), and a sorried theorem drags no body — whereas
        # pulling a def/structure/instance this way would drag its fields/value and
        # cascade through unrelated hierarchies (the CSS Pauli algebra, the attack
        # zoo, the CQState reference machinery). Data refs are real type-deps and
        # are handled by the `deps`/type-closure passes.
        for d in list(members.values()):
            if d.kind in _THEOREM_KINDS:
                continue
            body = _strip_comments(_apply_elision(d, "sorry"))
            for m in _BODY_IDENT_RE.finditer(body):
                raw = m.group(0)
                # A token still bare after Unicode-aware tokenization yet immediately
                # preceded by `.` is a dot-call on a NON-identifier receiver, e.g.
                # `(Φ.comp Ψ).comp` -> bare `comp` (receiver is `)`). Lean resolves it
                # through the receiver's type, so it is never a standalone short-name
                # reference; suffix-matching it against project theorems by last
                # segment is unsound. (Identifier receivers — incl. Unicode `ρ.method`
                # — are now captured whole and handled by the dotted branch below.)
                if m.start() > 0 and body[m.start() - 1] == ".":
                    continue
                if raw in _RHS_NOISE or raw in members:
                    continue
                seg = raw.rsplit(".", 1)[-1]
                cands = {raw} if raw in index else {
                    m for m in suffix_map.get(seg, set()) if m in index} - set(members)
                cands = {c for c in cands if index[c].kind in _THEOREM_KINDS}
                if not cands:
                    continue
                if len(cands) == 1:
                    pick = next(iter(cands))
                elif "." in raw:
                    # dotted `recv.method`: keep the overload whose receiver type
                    # matches `recv`'s binder type in THIS body (`atk :
                    # GeneralAttackLinear` -> `GeneralAttackLinear.neZeroEveDim`, not
                    # the sibling `SymmetrizedAttack`/`BobEveAttackLinear` overloads,
                    # which would each drag their attack structure).
                    recv = raw.rsplit(".", 1)[0].rsplit(".", 1)[-1]
                    th = _receiver_type_head(recv, body)
                    typed = {c for c in cands
                             if c.rsplit(".", 1)[0].rsplit(".", 1)[-1] == th} if th else set()
                    if len(typed) != 1:
                        continue
                    pick = next(iter(typed))
                else:
                    continue
                members[pick] = index[pick]
                added = True

        # Type-level closure: statement deps of the (sorried) theorems just pulled,
        # plus implicit type arguments not named verbatim.
        for d in dep_closure(index, list(members.keys())):
            if d.name not in members:
                members[d.name] = d
                added = True

        # Instances OF the helper classes only, with satisfiable deps.
        closure_modules = {d.module for d in members.values()}
        for name, d in index.items():
            if name in members or d.kind != "instance" or d.module not in closure_modules:
                continue
            if not (helper_classes & set(d.deps)):
                continue
            if all(satisfied(dep) for dep in d.deps):
                members[name] = d
                added = True
        if not added:
            break
    members_list = list(members.values())
    return members_list, _select_notations(module_notations, members_list, index)


def _module_import_order(
    modules, module_imports: dict[str, list[str]], project_modules: set[str]
) -> list[str]:
    """Leaf-first order of the closure's modules by the project import DAG
    (imported-before-importer), using transitive reachability so a pair linked
    only through a non-closure module is still ordered correctly."""
    modset = set(modules)

    def reachable(start: str) -> set[str]:
        seen, stack = set(), [start]
        while stack:
            m = stack.pop()
            for imp in module_imports.get(m, []):
                if imp in project_modules and imp not in seen:
                    seen.add(imp)
                    stack.append(imp)
        return seen

    deps = {m: (reachable(m) & modset) - {m} for m in modset}
    indeg = {m: len(deps[m]) for m in modset}
    dependents: dict[str, list[str]] = {m: [] for m in modset}
    for m, ds in deps.items():
        for d in ds:
            dependents[d].append(m)
    queue = deque(sorted(m for m in modset if indeg[m] == 0))
    order: list[str] = []
    while queue:
        m = queue.popleft()
        order.append(m)
        for u in sorted(dependents[m]):
            indeg[u] -= 1
            if indeg[u] == 0:
                queue.append(u)
    for m in sorted(modset - set(order)):
        order.append(m)
    return order


def _render_self_contained(
    targets: list[DeclInfo],
    members: list[DeclInfo],
    index: dict[str, DeclInfo],
    *,
    root_module: str = "",
    module_imports: dict[str, list[str]] | None = None,
    module_opens: dict[str, list[str]] | None = None,
    module_notations: dict[str, list] | None = None,
    module_variables: dict[str, list[str]] | None = None,
    module_context: dict[str, list[str]] | None = None,
    project_modules: set[str] | None = None,
    header: str = "",
) -> str:
    """Self-contained mini-library digest (the default).

    `import Mathlib` only; the project notation + decls re-declared verbatim in
    their real namespaces, leaf-first, proofs sorried. Compiles standalone with no
    real-vs-copy split (nothing project-level is imported), so the shown notation
    and defs elaborate exactly as in the library.
    """
    module_imports = module_imports or {}
    module_opens = module_opens or {}
    module_notations = module_notations or {}
    module_variables = module_variables or {}
    project_modules = project_modules or set()
    target_names = {t.name for t in targets}

    # The genuine type-closure (banner + tree reflect THIS — the theorem's real
    # dependency surface). `_expand_and_select` then adds notation/instance SUPPORT
    # decls that aren't type-dependencies but must be re-declared for the file to
    # compile; those are emitted as code but counted/labelled separately, never
    # folded into the "dependency closure".
    closure_members = list(members)
    closure_names = {m.name for m in closure_members}

    members, selected = _expand_and_select(members, index, module_notations)
    # Drop field projections pulled via deps: the structure/class re-declaration
    # regenerates them, and a no-source projection would synthesize a colliding
    # stub (e.g. `theorem GeneralAttack.eveDim_pos` vs the class's field).
    proj_names = _projection_names(members)
    members = [m for m in members if m.name not in proj_names or m.name in target_names]
    selected = _dedup_notations(selected)
    support = [m for m in members if m.name not in closure_names]

    closure_modules = {d.module for d in members}
    ext_imports = _external_imports(closure_modules, module_imports, project_modules)

    project_ns = _project_namespaces(project_modules, root_module)
    populated_ns: set[str] = set()
    for d in members:
        populated_ns |= _ns_prefixes(d.decl_namespace)

    by_module: dict[str, list[DeclInfo]] = {}
    for d in members:
        by_module.setdefault(d.module, []).append(d)

    lines = _digest_banner(targets, closure_members, root_module, header,
                           "self-contained mini-library: import Mathlib only; "
                           "notation + decls re-declared in real namespaces, leaf-first")
    if support:
        lines.append(f"-- (+ {len(support)} notation/instance support decls re-declared so "
                     f"the file compiles — not part of the dependency closure.)")
    lines.append("")
    lines.append("import Mathlib" if not ext_imports else "")
    for imp in ext_imports:
        lines.append(f"import {imp}")
    lines.append("")
    lines.extend(_preamble_options())
    lines.append("")
    lines.extend(_dep_tree(targets, closure_members, index))
    lines.append("")
    lines.append("noncomputable section")
    lines.append("")

    # Forward-declare every namespace the digest re-populates, so a module's
    # `open <project ns>` resolves even when that namespace is first populated
    # later (or within the same module). Re-declaring decls means the namespaces
    # don't exist until their decls are emitted; an `open` registers a search
    # path, so decls added after it are still found.
    all_ns = sorted({d.decl_namespace for d in members if d.decl_namespace})
    if all_ns:
        lines.append("-- Forward-declared namespaces (so cross-module opens resolve).")
        for ns in all_ns:
            lines.append(f"namespace {ns} end {ns}")
        lines.append("")

    for mod in _module_import_order(closure_modules, module_imports, project_modules):
        decls = by_module[mod]
        mshort = module_short(mod, root_module)
        lines.append(f"-- {'═' * 4} from {mshort} {'═' * 4}")
        # Opens go at module level (no enclosing namespace); they persist into the
        # per-decl namespaces below. A decl is placed under ITS OWN decl_namespace,
        # not the module's primary one — a module can define decls in foreign
        # namespaces (e.g. `Quantum.Operators.DensityOp.tensor` lives in module
        # `Quantum.TensorProducts.Basic`), and the re-declared name must match.
        opens = _filter_opens(module_opens.get(mod, []), project_ns, populated_ns)
        for opn in opens:
            lines.append(opn)
        for var in module_variables.get(mod, []):
            lines.append(var)
        lines.append("")

        # Interleave this module's selected notations and decls by source line, so
        # helper defs precede the notations that reference them, which precede the
        # decls that use them (the ordering the de-risk validated).
        items: list[tuple] = []
        for meta in selected.get(mod, []):
            items.append((meta["line"], 0, "nota", meta))
        for d in decls:
            items.append((d.line or 0, 1, "decl", d))
        items.sort(key=lambda x: (x[0], x[1]))
        current_ns: str | None = None
        for _line, _rank, kind, obj in items:
            want_ns = (obj.decl_namespace or "") if kind == "decl" else (current_ns or "")
            if want_ns != (current_ns or ""):
                if current_ns:
                    lines.append(f"end {current_ns}")
                if want_ns:
                    lines.append(f"namespace {want_ns}")
                current_ns = want_ns or None
            if kind == "nota":
                lines.append(obj["text"])
                lines.append("")
            else:
                tag = "◾ TARGET" if obj.name in target_names else "◾"
                lines.append(f"-- {tag} {display_name(obj)} ({mshort}:{obj.line or '?'})")
                lines.append(_render_decl_source(obj))
                lines.append("")
        if current_ns:
            lines.append(f"end {current_ns}")
        lines.append("")

    lines.append("end")  # close `noncomputable section`
    return "\n".join(lines)


# ===========================================================================
# import + #print/#check digest ("print" mode)
# ===========================================================================
#
# Import the real closure modules and, per decl, show: the docstring, the
# verbatim source slice (as authored, in a foldable comment), and a `#check`
# (theorems) / `#print` (defs/structures) of the IMPORTED decl. The first two
# are the author's view; the third is the elaborator's ground truth — and the
# delta between them surfaces coercions, vacuous hypotheses, instance surprises.
# Trivially robust (importing the library can't fail to compile), and needs only
# the type-level closure to display — no re-declaration machinery.


def _dep_tree(targets: list[DeclInfo], members: list[DeclInfo],
              index: dict[str, DeclInfo]) -> list[str]:
    """An indented dependency tree over the shown closure (a `*` marks a node
    already expanded above, so the tree stays finite on shared/recursive deps)."""
    member_names = {m.name for m in members}
    out = ["/-! ## Dependency tree  (`*` = expanded above)", ""]
    expanded: set[str] = set()

    def walk(name: str, prefix: str, last: bool) -> None:
        d = index.get(name)
        label = display_name(d) if d else name.rsplit(".", 1)[-1]
        conn = "└─ " if last else "├─ "
        if name in expanded:
            out.append(f"{prefix}{conn}{label} *")
            return
        out.append(f"{prefix}{conn}{label}")
        expanded.add(name)
        if d is None:
            return
        kids = sorted({dep for dep in d.deps if dep in member_names and dep != name},
                      key=lambda x: (index[x].module, index[x].line or 0, x))
        child_prefix = prefix + ("   " if last else "│  ")
        for i, k in enumerate(kids):
            walk(k, child_prefix, i == len(kids) - 1)

    for t in targets:
        walk(t.name, "", True)
    out.append("-/")
    return out


def _strip_leading_doc(src: str) -> str:
    """Drop a leading `/-- … -/` docstring from a source slice (it's shown
    separately) — a nested block comment may itself contain `-/`, so scan past
    matched `/-` … `-/` pairs."""
    s = src.lstrip()
    if not s.startswith("/-"):
        return src
    depth, i, n = 0, 0, len(s)
    while i < n:
        if s[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif s[i:i + 2] == "-/":
            depth -= 1
            i += 2
            if depth == 0:
                return s[i:].lstrip("\n")
        else:
            i += 1
    return src


def _source_comment(src: str) -> list[str]:
    """The verbatim slice as line-comments (safe: a block comment would be closed
    early by a `-/` inside a nested docstring)."""
    lines = ["-- ┌ source (as authored):"]
    lines += [f"-- │ {ln}" for ln in src.splitlines()]
    lines.append("-- └")
    return lines


def _print_dumps_noise(d: DeclInfo) -> bool:
    """True when `#print d` would dump an unreadable compiled body, so the renderer
    should fall back to `#check` (type) instead (the body is in the source slice).

    Applies only to `def`/`instance` — for structures/classes/inductives/abbrevs
    `#print` is bounded and valuable (field flattening, reduced type). A def is
    noisy if it's RECURSIVE (its compiled value is `brecOn`/`*.rec` machinery, not
    the source) or its body is LARGE (a screenful of elaborated term)."""
    if d.kind not in ("def", "instance"):
        return False
    if d.name in (d.deps or []):
        return True
    return (d.source_text or "").count("\n") > 24


def _render_print(
    targets: list[DeclInfo],
    members: list[DeclInfo],
    index: dict[str, DeclInfo],
    *,
    root_module: str = "",
    header: str = "",
    show_source: bool = True,
) -> str:
    """Import + #print/#check digest (see module comment above). ``show_source``
    toggles the authored-source slice (the dep-tree + #print/#check stay)."""
    target_names = {t.name for t in targets}
    proj = _projection_names(members)
    members = [m for m in members if m.name not in proj or m.name in target_names]
    closure_modules = sorted({d.module for d in members})

    lines = _digest_banner(targets, members, root_module, header,
                           "import + #print/#check: real decls imported; source slice "
                           "(authored) shown beside the elaborated form (ground truth)")
    lines.append("")
    for m in closure_modules:
        lines.append(f"import {m}")
    lines.append("")
    lines.append("-- #check/#print show the ELABORATED form (the elaborator's ground truth):")
    lines.append("-- the pretty-printer may insert coercions (↑), expand notation, or drop")
    lines.append("-- redundant parens, so it can differ from the authored source shown per decl.")
    lines.append("")
    lines.extend(_dep_tree(targets, members, index))
    lines.append("")

    for d in _decl_topo_order(members):   # leaf-first, target last
        mshort = module_short(d.module, root_module)
        tag = "◾ TARGET" if d.name in target_names else "◾"
        lines.append(f"-- {'═' * 4} {tag} {display_name(d)} ({mshort}:{d.line or '?'}) {'═' * 4}")
        # Docstring as a PLAIN comment — a real `/-- … -/` must attach to a decl,
        # but the next thing here is a `#print`/`#check` command, not a decl.
        if d.docstring:
            for i, ln in enumerate(d.docstring.rstrip().splitlines()):
                lines.append(f"-- 🗎 {ln}" if i == 0 else f"--   {ln}")
        if show_source and d.source_text:
            lines.extend(_source_comment(_strip_leading_doc(_apply_elision(d, "⋯"))))
        # Private decls aren't accessible across an import (and their `_private.…0.…`
        # name doesn't even parse in a command), so show only the authored slice.
        # Otherwise: #print dumps a theorem's proof term; #check shows its statement.
        if d.is_private:
            lines.append("-- (private to its module — elaborated form not available across import)")
        elif d.kind in _THEOREM_KINDS:
            lines.append(f"#check @{d.name}")
        elif _print_dumps_noise(d):
            # `#print` on a recursive or very large def dumps the compiled body
            # (`brecOn`/`Nat.rec` machinery or a screenful of elaborated term) — its
            # value is unreadable. Show the type via `#check`; the body is already
            # in the source slice above.
            lines.append(f"-- (large/recursive def — #print body omitted; see source slice. type:)")
            lines.append(f"#check @{d.name}")
        else:
            lines.append(f"#print {d.name}")
        lines.append("")
    return "\n".join(lines)


def comparator_config(
    targets: list[DeclInfo],
    closure: list[DeclInfo],
    *,
    challenge_module: str,
    permitted_axioms: list[str],
    definition_names: list[str] | None = None,
) -> dict:
    """Build a github.com/leanprover/comparator config.json payload.

    The digest imports the real dependency definitions (they are not sorried
    holes), so ``definition_names`` is empty by default — comparator only
    pins the target theorem statements + axiom usage. Pass an explicit list
    only when the challenge genuinely leaves defs open for the solver to fill.
    """
    target_names = [t.name for t in targets]
    solution_modules = sorted({t.module for t in targets})
    return {
        "challenge_module": challenge_module,
        "solution_module": solution_modules[0] if len(solution_modules) == 1 else solution_modules,
        "theorem_names": target_names,
        "permitted_axioms": permitted_axioms,
        "definition_names": list(definition_names or []),
    }
