"""Shared utilities for sorry-tree and sig-tree."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Optional


def log(msg: str) -> None:
    """Print status message to stderr."""
    print(msg, file=sys.stderr)


def detect_root_module(lake_root: Path) -> str:
    """Auto-detect root module from lakefile.toml or lakefile.lean."""
    try:
        import tomllib
    except ModuleNotFoundError:
        try:
            import tomli as tomllib  # type: ignore[no-redef]
        except ModuleNotFoundError:
            tomllib = None  # type: ignore[assignment]

    lakefile_toml = lake_root / "lakefile.toml"
    if lakefile_toml.exists() and tomllib is not None:
        try:
            data = tomllib.loads(lakefile_toml.read_text())
            for lib in data.get("lean_lib", []):
                name = lib.get("name")
                if name:
                    return name
        except Exception:
            pass

    lakefile_lean = lake_root / "lakefile.lean"
    if lakefile_lean.exists():
        try:
            text = lakefile_lean.read_text()
            m = re.search(r"lean_lib\s+(\w+)", text)
            if m:
                return m.group(1)
        except Exception:
            pass

    return ""


def _private_short_name(name: str) -> Optional[str]:
    """Extract readable name from _private.Module.Path.0.Namespace.name."""
    if not name.startswith("_private."):
        return None
    parts = name.split(".")
    for i in range(len(parts) - 1, -1, -1):
        if parts[i].isdigit():
            return ".".join(parts[i + 1:])
    return name


def module_short(module: str, root_module: str = "") -> str:
    """Shorten 'RootModule.Math.Entropy' to 'Math.Entropy'."""
    if root_module and module.startswith(root_module + "."):
        return module[len(root_module) + 1:]
    return module


def find_decl(index: dict, name: str) -> list:
    """Find declaration by exact or suffix match."""
    if name in index:
        return [index[name]]
    return [d for n, d in index.items() if n.endswith("." + name)]


def find_by_module(index: dict, module_query: str,
                   root_module: str = "") -> list:
    """Find declarations in a specific module.

    Accepts: 'InfoTheory/Measurement/POVM', 'InfoTheory.Measurement.POVM',
    or 'RootModule.InfoTheory.Measurement.POVM'.
    """
    query = module_query.replace("/", ".").removesuffix(".lean")
    if root_module and not query.startswith(root_module + "."):
        query = root_module + "." + query
    return [d for d in index.values() if d.module == query]
