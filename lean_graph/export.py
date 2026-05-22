"""Run Lean exporters and load declaration databases.

Supports incremental caching: re-runs the Lean export when project oleans,
exporter scripts, or cached module membership have changed.
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Optional


EXPORT_DECLS_LEAN = Path(__file__).resolve().parent / "lean" / "ExportDecls.lean"
EXPORT_SIGS_LEAN = Path(__file__).resolve().parent / "lean" / "ExportSigs.lean"


def run_lean_export(
    lake_root: Path,
    root_module: str,
    export_lean: Path,
    timeout: Optional[float] = None,
) -> dict:
    """Run a Lean exporter script and return the parsed JSON.

    Requires the project to be built (``lake build`` first).
    """
    script = str(export_lean)
    cmd = ["lake", "env", "lean", "--run", script, root_module]
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
    """Load a previously exported JSON."""
    with open(path) as f:
        return json.load(f)


# ---------------------------------------------------------------------------
# Incremental caching
# ---------------------------------------------------------------------------

def _olean_dir(lake_root: Path) -> Path:
    """Return the olean build directory."""
    return lake_root / ".lake" / "build" / "lib"


def _latest_olean_mtime(lake_root: Path, root_module: str) -> float:
    """Find the most recent olean modification time for project modules."""
    olean_root = _olean_dir(lake_root) / "lean" / root_module
    if not olean_root.is_dir():
        olean_root = _olean_dir(lake_root) / root_module
    if not olean_root.is_dir():
        return 0.0

    latest = 0.0
    for p in olean_root.rglob("*.olean"):
        mt = p.stat().st_mtime
        if mt > latest:
            latest = mt

    root_olean = olean_root.with_suffix(".olean")
    if root_olean.exists():
        mt = root_olean.stat().st_mtime
        if mt > latest:
            latest = mt

    return latest


def _any_olean_deleted(lake_root: Path, root_module: str,
                       cached_modules: set[str]) -> bool:
    """Check if any module in the cache no longer has an olean."""
    olean_base = _olean_dir(lake_root) / "lean"
    for mod in cached_modules:
        olean_path = olean_base / (mod.replace(".", "/") + ".olean")
        if not olean_path.exists():
            return True
    return False


def export_cached(
    lake_root: Path,
    root_module: str,
    cache_path: Path,
    export_lean: Path,
    timeout: Optional[float] = None,
) -> dict:
    """Export declarations with caching.

    Re-exports when project oleans or the exporter script changed.

    Returns the declaration data dict.
    """
    needs_export = True

    if cache_path.exists():
        cache_mtime = cache_path.stat().st_mtime
        latest_olean = _latest_olean_mtime(lake_root, root_module)
        exporter_mtime = export_lean.stat().st_mtime

        if (
            latest_olean > 0
            and latest_olean <= cache_mtime
            and exporter_mtime <= cache_mtime
        ):
            try:
                cached_data = load_from_file(cache_path)
                cached_modules = {d["module"] for d in cached_data["declarations"]}
                if not _any_olean_deleted(lake_root, root_module, cached_modules):
                    needs_export = False
                    print(f"Cache is up to date ({len(cached_data['declarations'])} declarations)",
                          file=sys.stderr)
                    return cached_data
                else:
                    print("Detected deleted modules, re-exporting...", file=sys.stderr)
            except (json.JSONDecodeError, KeyError, OSError):
                pass  # Corrupt cache, re-export
        elif exporter_mtime > cache_mtime:
            print("Exporter changed, re-exporting...", file=sys.stderr)

    if needs_export:
        print(f"Oleans changed, re-exporting from {root_module}...",
              file=sys.stderr, flush=True)
        data = run_lean_export(lake_root, root_module, export_lean, timeout)
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        cache_path.write_text(json.dumps(data) + "\n")
        print(f"Exported {len(data['declarations'])} declarations (cached)",
              file=sys.stderr)
        return data

    raise RuntimeError("Unexpected state in export_cached")


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
