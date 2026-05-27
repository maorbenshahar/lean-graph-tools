"""Run Lean exporters and load declaration databases.

Supports incremental caching:
- Cache schema v2 records per-module olean mtimes alongside the flat
  declarations list. After a `lake build`, only modules whose olean mtimes
  exceed the cached value get re-exported; the result is merged into the
  existing cache. Falls back to a full rebuild when no cache exists, when the
  exporter script changed, or when ``force_full=True``.
- Caches written by previous versions (no ``schema_version`` key) are ignored
  and replaced by a fresh v2 cache on the next call.
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Optional


EXPORT_DECLS_LEAN = Path(__file__).resolve().parent / "lean" / "ExportDecls.lean"
EXPORT_SIGS_LEAN = Path(__file__).resolve().parent / "lean" / "ExportSigs.lean"

SCHEMA_VERSION = 2


def run_lean_export(
    lake_root: Path,
    root_module: str,
    export_lean: Path,
    timeout: Optional[float] = None,
    modules: Optional[Iterable[str]] = None,
) -> dict:
    """Run a Lean exporter script and return the parsed JSON.

    Requires the project to be built (``lake build`` first).

    When ``modules`` is given, the exporter is invoked with that module list as
    positional args and emits declarations only from those modules. With no
    ``modules``, every project-local declaration is emitted (full export).
    """
    script = str(export_lean)
    cmd = ["lake", "env", "lean", "--run", script, root_module]
    if modules is not None:
        cmd.extend(modules)
    result = subprocess.run(
        cmd,
        cwd=lake_root,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if result.returncode != 0:
        name = export_lean.stem
        print(f"ERROR: {name} failed (exit {result.returncode})", file=sys.stderr)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        raise RuntimeError(f"{name} failed: {result.stderr[:200]}")

    return json.loads(result.stdout)


def load_from_file(path: Path) -> dict:
    """Load a previously exported JSON.

    Returns the raw dict on disk. Consumers iterate ``data["declarations"]``
    which is present in both v1 and v2. Schema-version-specific keys are
    ignored by consumers.
    """
    with open(path) as f:
        return json.load(f)


# ---------------------------------------------------------------------------
# Olean mtime helpers
# ---------------------------------------------------------------------------

def _olean_dir(lake_root: Path) -> Path:
    """Return the olean build directory."""
    return lake_root / ".lake" / "build" / "lib"


def _olean_root(lake_root: Path, root_module: str) -> Optional[Path]:
    """Return the directory that holds ``<root_module>/**/*.olean``.

    Newer Lake layouts place project oleans under ``.lake/build/lib/lean/<root>/``;
    older ones use ``.lake/build/lib/<root>/``. Try both.
    """
    candidate = _olean_dir(lake_root) / "lean" / root_module
    if candidate.is_dir():
        return candidate
    candidate = _olean_dir(lake_root) / root_module
    if candidate.is_dir():
        return candidate
    return None


def _per_module_olean_mtimes(lake_root: Path, root_module: str) -> dict[str, float]:
    """Return a mapping ``{module_name: olean_mtime}`` for every project module.

    The module name is reconstructed from the relative path inside the olean
    root, dot-separated, prefixed by ``<root_module>``. Missing olean root
    yields an empty dict.
    """
    olean_root = _olean_root(lake_root, root_module)
    if olean_root is None:
        return {}

    mtimes: dict[str, float] = {}
    # Sub-modules: olean_root/<sub>/.../File.olean → <root_module>.<sub>...<File>
    for olean_path in olean_root.rglob("*.olean"):
        rel = olean_path.relative_to(olean_root).with_suffix("")
        module_name = ".".join((root_module, *rel.parts))
        mtimes[module_name] = olean_path.stat().st_mtime

    # Root olean (sibling of the directory): olean_root.with_suffix(".olean") → <root_module>
    root_olean = olean_root.with_suffix(".olean")
    if root_olean.exists():
        mtimes[root_module] = root_olean.stat().st_mtime

    return mtimes


def _diff_modules(
    cached_mtimes: dict[str, float],
    current_mtimes: dict[str, float],
) -> tuple[set[str], set[str]]:
    """Compute (to_export, to_delete).

    ``to_export``: modules present in ``current_mtimes`` whose mtime is newer
    than the cached mtime (or which are absent from the cache entirely).
    ``to_delete``: modules present in the cache but no longer in
    ``current_mtimes`` (their oleans were removed).
    """
    to_export: set[str] = set()
    for mod, mtime in current_mtimes.items():
        cached = cached_mtimes.get(mod)
        if cached is None or mtime > cached:
            to_export.add(mod)
    to_delete = set(cached_mtimes.keys()) - set(current_mtimes.keys())
    return to_export, to_delete


# ---------------------------------------------------------------------------
# Cache shape (v2)
# ---------------------------------------------------------------------------

def _new_v2_cache(
    root_module: str,
    exporter_mtime: float,
    module_mtimes: dict[str, float],
    declarations: list,
) -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "root_module": root_module,
        "exporter_mtime": exporter_mtime,
        "module_mtimes": dict(module_mtimes),
        "declaration_count": len(declarations),
        "declarations": list(declarations),
    }


def _is_v2(cache: dict) -> bool:
    return cache.get("schema_version") == SCHEMA_VERSION


def _merge_cache(
    old: dict,
    partial: dict,
    current_mtimes: dict[str, float],
    re_exported: set[str],
    deletions: set[str],
    canonical_modules: Optional[set[str]] = None,
) -> dict:
    """Merge ``partial`` (declarations for modules in ``re_exported``) into
    ``old`` (a v2 cache), dropping declarations for ``deletions``, and
    refreshing ``module_mtimes`` for re-exported modules.

    ``canonical_modules`` (if given) is the authoritative project module set
    as reported by the exporter via ``project_modules``. Any cached entry for
    a module not in this set is also dropped — this catches ghost modules
    whose oleans linger on disk after their import was removed.
    """
    # Drop declarations for re-exported and deleted modules.
    drop = set(re_exported) | set(deletions)
    if canonical_modules is not None:
        # Drop anything no longer reachable from the project root.
        for m in old.get("module_mtimes", {}):
            if m not in canonical_modules:
                drop.add(m)
    kept = [d for d in old["declarations"] if d["module"] not in drop]

    # Merge in the freshly exported declarations.
    new_decls = list(partial.get("declarations", []))

    # Refresh module_mtimes: keep entries for modules that survived, replace
    # entries for re-exported modules with current mtimes, drop the rest.
    module_mtimes: dict[str, float] = {
        m: t for m, t in old.get("module_mtimes", {}).items() if m not in drop
    }
    for m in re_exported:
        if m not in current_mtimes:
            continue
        # Don't re-add a re-exported module that the exporter says isn't
        # canonical (it was a ghost we asked about but isn't really in the project).
        if canonical_modules is not None and m not in canonical_modules:
            continue
        module_mtimes[m] = current_mtimes[m]

    merged = list(kept) + new_decls
    return {
        "schema_version": SCHEMA_VERSION,
        "root_module": old["root_module"],
        "exporter_mtime": old["exporter_mtime"],
        "module_mtimes": module_mtimes,
        "declaration_count": len(merged),
        "declarations": merged,
    }


def _write_cache(cache_path: Path, cache: dict) -> None:
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    cache_path.write_text(json.dumps(cache) + "\n")


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def export_cached(
    lake_root: Path,
    root_module: str,
    cache_path: Path,
    export_lean: Path,
    timeout: Optional[float] = None,
    *,
    force_full: bool = False,
) -> dict:
    """Export declarations with incremental caching.

    Decision tree:
    1. ``force_full`` → full export, replace cache.
    2. No cache, or cache is not v2, or exporter script changed → full export,
       replace cache.
    3. ``_diff_modules`` empty → cache hit, return as-is.
    4. Otherwise → partial export for changed modules, merge with cache,
       persist, return.

    Returns the merged data dict. The dict carries v2 metadata
    (``schema_version``, ``module_mtimes``, ``exporter_mtime``) but its
    ``declarations`` list is the same shape consumers already expect.
    """
    exporter_mtime = export_lean.stat().st_mtime

    if force_full:
        return _do_full_export(
            lake_root, root_module, cache_path, export_lean, timeout, exporter_mtime,
            reason="forced full rebuild",
        )

    cache: Optional[dict] = None
    if cache_path.exists():
        try:
            cache = load_from_file(cache_path)
        except (json.JSONDecodeError, OSError):
            cache = None

    if cache is None or not _is_v2(cache):
        return _do_full_export(
            lake_root, root_module, cache_path, export_lean, timeout, exporter_mtime,
            reason=("no cache" if cache is None else "cache schema mismatch"),
        )

    if cache.get("exporter_mtime", 0.0) < exporter_mtime:
        return _do_full_export(
            lake_root, root_module, cache_path, export_lean, timeout, exporter_mtime,
            reason="exporter script changed",
        )

    current_mtimes = _per_module_olean_mtimes(lake_root, root_module)
    if not current_mtimes:
        # Oleans missing entirely — let the caller's build-if-needed path
        # surface a clearer error. Fall back to full export which will fail
        # with the same diagnostic the legacy path produced.
        return _do_full_export(
            lake_root, root_module, cache_path, export_lean, timeout, exporter_mtime,
            reason="no oleans found",
        )

    to_export, to_delete = _diff_modules(cache.get("module_mtimes", {}), current_mtimes)
    if not to_export and not to_delete:
        print(
            f"Cache is up to date ({cache['declaration_count']} declarations)",
            file=sys.stderr,
        )
        return cache

    print(
        f"Cache stale: {len(to_export)} module(s) to re-export, "
        f"{len(to_delete)} module(s) to drop. Running partial export...",
        file=sys.stderr,
        flush=True,
    )
    canonical_modules: Optional[set[str]] = None
    if to_export:
        partial = run_lean_export(
            lake_root, root_module, export_lean, timeout, modules=sorted(to_export)
        )
        # The exporter reports the canonical module set (everything reachable
        # via importModules). Use it to garbage-collect ghost cache entries
        # whose oleans linger on disk after an import was removed. Treat the
        # key being ABSENT as "exporter doesn't tell us, don't GC anything"
        # (defensive against older exporter binaries).
        if "project_modules" in partial:
            canonical_modules = set(partial["project_modules"])
    else:
        partial = {"declarations": []}

    merged = _merge_cache(
        cache, partial, current_mtimes, to_export, to_delete,
        canonical_modules=canonical_modules,
    )
    _write_cache(cache_path, merged)
    # Ghosts: modules removed from module_mtimes beyond the explicit olean
    # deletions. They came from the canonical_modules garbage-collection pass.
    removed_modules = set(cache.get("module_mtimes", {})) - set(merged.get("module_mtimes", {}))
    ghosts_dropped = len(removed_modules - to_delete)
    extra = f", -{ghosts_dropped} ghost modules" if ghosts_dropped else ""
    print(
        f"Cache updated ({merged['declaration_count']} declarations, "
        f"+{len(partial.get('declarations', []))} new, "
        f"-{len(to_delete)} deleted modules{extra})",
        file=sys.stderr,
    )
    return merged


def _do_full_export(
    lake_root: Path,
    root_module: str,
    cache_path: Path,
    export_lean: Path,
    timeout: Optional[float],
    exporter_mtime: float,
    reason: str,
) -> dict:
    print(f"Full export ({reason})...", file=sys.stderr, flush=True)
    data = run_lean_export(lake_root, root_module, export_lean, timeout)
    disk_mtimes = _per_module_olean_mtimes(lake_root, root_module)
    # Filter the disk walk by what the exporter actually saw. Ghost oleans
    # (whose .lean was unimported but Lake left the .olean on disk) would
    # otherwise appear in module_mtimes without any corresponding declarations,
    # making the cache internally inconsistent.
    if "project_modules" in data:
        canonical = set(data["project_modules"])
        module_mtimes = {m: t for m, t in disk_mtimes.items() if m in canonical}
    else:
        module_mtimes = disk_mtimes
    cache = _new_v2_cache(
        root_module=root_module,
        exporter_mtime=exporter_mtime,
        module_mtimes=module_mtimes,
        declarations=data.get("declarations", []),
    )
    _write_cache(cache_path, cache)
    print(
        f"Exported {cache['declaration_count']} declarations (cached)",
        file=sys.stderr,
    )
    return cache


# ---------------------------------------------------------------------------
# Consumer helpers
# ---------------------------------------------------------------------------

def recompute_transitive_sorry(data: dict) -> dict:
    """Recompute has_sorry (transitive) from contains_sorry (direct) + deps.

    Modifies the data in-place and returns it.
    This is pure Python DFS -- instant even for large projects.
    """
    index = {d["name"]: d for d in data["declarations"]}

    memo: dict[str, bool] = {}

    def _has_sorry(name: str) -> bool:
        if name in memo:
            return memo[name]
        if name not in index:
            memo[name] = False
            return False
        decl = index[name]
        if decl["contains_sorry"]:
            memo[name] = True
            return True
        # Prevent cycles
        memo[name] = False
        for dep in decl.get("deps", []):
            if _has_sorry(dep):
                memo[name] = True
                return True
        return False

    for d in data["declarations"]:
        d["has_sorry"] = _has_sorry(d["name"])

    return data
