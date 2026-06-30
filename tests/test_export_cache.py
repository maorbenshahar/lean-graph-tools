"""Tests for the incremental export cache in lean_graph.export."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable, Optional
from unittest.mock import patch

import pytest

from lean_graph import export as exp


# ---------------------------------------------------------------------------
# Fixture: a tmp_path "lake project" with fake oleans and a stub exporter
# ---------------------------------------------------------------------------

@pytest.fixture
def fake_project(tmp_path: Path) -> dict[str, Any]:
    """Materialise a lake-root with a few olean files under the standard layout.

    Returns a dict with the paths and helpers for tests.
    """
    lake_root = tmp_path / "proj"
    root_module = "Proj"
    olean_root = lake_root / ".lake" / "build" / "lib" / "lean" / root_module
    olean_root.mkdir(parents=True)

    # Create a couple of project oleans at known mtimes.
    modules = {
        f"{root_module}.Foo": olean_root / "Foo.olean",
        f"{root_module}.Sub.Bar": olean_root / "Sub" / "Bar.olean",
    }
    for path in modules.values():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"")

    # Stub exporter "script" so its mtime is well-defined.
    export_lean = tmp_path / "ExportDecls.lean"
    export_lean.write_text("-- stub\n")

    cache_path = lake_root / ".lake" / "decls_cache.json"

    def set_olean_mtime(module_name: str, mtime: float) -> None:
        # module_name like "Proj.Foo" → file at olean_root/Foo.olean
        rel = module_name[len(root_module) + 1 :]  # strip "Proj."
        path = olean_root / Path(*rel.split(".")).with_suffix(".olean")
        # touch with target mtime
        import os
        os.utime(path, (mtime, mtime))

    return {
        "lake_root": lake_root,
        "root_module": root_module,
        "olean_root": olean_root,
        "modules": modules,
        "export_lean": export_lean,
        "cache_path": cache_path,
        "set_olean_mtime": set_olean_mtime,
    }


def _decl(name: str, module: str, **extra: Any) -> dict[str, Any]:
    """Helper to construct a minimal declaration dict like the Lean exporter emits."""
    base = {
        "name": name,
        "kind": "def",
        "module": module,
        "has_sorry": False,
        "contains_sorry": False,
        "is_private": False,
        "deps": [],
    }
    base.update(extra)
    return base


# ---------------------------------------------------------------------------
# Pure-function tests
# ---------------------------------------------------------------------------

def test_per_module_olean_mtimes_returns_known_modules(fake_project) -> None:
    mtimes = exp._per_module_olean_mtimes(
        fake_project["lake_root"], fake_project["root_module"]
    )
    assert set(mtimes.keys()) == {"Proj.Foo", "Proj.Sub.Bar"}


def test_per_module_olean_mtimes_missing_olean_root_returns_empty(tmp_path: Path) -> None:
    mtimes = exp._per_module_olean_mtimes(tmp_path / "nothing", "Proj")
    assert mtimes == {}


def test_diff_modules_detects_new_changed_and_deleted() -> None:
    cached = {"Proj.A": 100.0, "Proj.B": 200.0, "Proj.C": 300.0}
    current = {"Proj.A": 100.0, "Proj.B": 250.0, "Proj.D": 400.0}  # B changed, C gone, D new

    to_export, to_delete = exp._diff_modules(cached, current)
    assert to_export == {"Proj.B", "Proj.D"}
    assert to_delete == {"Proj.C"}


def test_diff_modules_empty_when_no_changes() -> None:
    cached = {"Proj.A": 100.0}
    current = {"Proj.A": 100.0}
    to_export, to_delete = exp._diff_modules(cached, current)
    assert to_export == set()
    assert to_delete == set()


def test_merge_cache_preserves_unchanged_modules() -> None:
    old = exp._new_cache(
        root_module="Proj",
        exporter_mtime=1.0,
        module_mtimes={"Proj.A": 100.0, "Proj.B": 200.0},
        declarations=[_decl("Proj.A.foo", "Proj.A"), _decl("Proj.B.bar", "Proj.B")],
        data={},
    )
    partial = {"declarations": [_decl("Proj.B.baz", "Proj.B")]}
    current = {"Proj.A": 100.0, "Proj.B": 250.0}

    merged = exp._merge_cache(old, partial, current, re_exported={"Proj.B"}, deletions=set())
    names = sorted(d["name"] for d in merged["declarations"])
    assert names == ["Proj.A.foo", "Proj.B.baz"]
    assert merged["module_mtimes"] == {"Proj.A": 100.0, "Proj.B": 250.0}
    assert merged["declaration_count"] == 2


def test_merge_cache_drops_deletions() -> None:
    old = exp._new_cache(
        root_module="Proj",
        exporter_mtime=1.0,
        module_mtimes={"Proj.A": 100.0, "Proj.B": 200.0},
        declarations=[_decl("Proj.A.foo", "Proj.A"), _decl("Proj.B.bar", "Proj.B")],
        data={},
    )
    partial = {"declarations": []}
    current = {"Proj.A": 100.0}  # Proj.B removed

    merged = exp._merge_cache(old, partial, current, re_exported=set(), deletions={"Proj.B"})
    assert [d["name"] for d in merged["declarations"]] == ["Proj.A.foo"]
    assert "Proj.B" not in merged["module_mtimes"]


# ---------------------------------------------------------------------------
# export_cached decision tree (with run_lean_export stubbed out)
# ---------------------------------------------------------------------------

def _stub_run_lean_export_factory(
    declarations_by_module: dict[str, list[dict[str, Any]]],
    calls: list[dict[str, Any]],
    project_modules: Optional[list[str]] = None,
):
    """Return a stub that records each call and returns declarations matching the filter.

    The stub's response includes ``project_modules`` mirroring what the real
    Lean exporter emits — every module reachable via ``importModules root``.
    Tests can override this to simulate cases where ``importModules`` no longer
    reaches some module (an import was removed) while its olean is still on disk.
    """
    if project_modules is None:
        canonical = sorted(declarations_by_module.keys())
    else:
        canonical = list(project_modules)
    def stub(
        lake_root: Path,
        root_module: str,
        export_lean: Path,
        timeout: Optional[float] = None,
        modules: Optional[Iterable[str]] = None,
    ) -> dict[str, Any]:
        modules_list = sorted(modules) if modules is not None else None
        calls.append({"modules": modules_list})
        if modules_list is None:
            decls = [d for mod_decls in declarations_by_module.values() for d in mod_decls]
        else:
            decls = [d for m in modules_list for d in declarations_by_module.get(m, [])]
        return {
            "root_module": root_module,
            "declaration_count": len(decls),
            "declarations": decls,
            "project_modules": canonical,
        }
    return stub


def test_full_export_when_no_cache(fake_project) -> None:
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        result = exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # One call, with no module filter (full export).
    assert len(calls) == 1
    assert calls[0]["modules"] is None
    # v2 cache written.
    on_disk = json.loads(fake_project["cache_path"].read_text())
    assert on_disk["schema_version"] == exp.SCHEMA_VERSION
    assert set(on_disk["module_mtimes"].keys()) == {"Proj.Foo", "Proj.Sub.Bar"}
    assert result["declaration_count"] == 2


def test_cache_hit_skips_export(fake_project) -> None:
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )
        # Second call: no oleans touched, exporter unchanged → cache hit, no new subprocess call.
        result2 = exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    assert len(calls) == 1  # only the initial full export
    assert result2["declaration_count"] == 2


def test_partial_export_when_one_module_changed(fake_project) -> None:
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # Now mutate Proj.Foo: replace its declarations + bump olean mtime.
    decls_by_mod["Proj.Foo"] = [
        _decl("Proj.Foo.a_renamed", "Proj.Foo"),
        _decl("Proj.Foo.new_decl", "Proj.Foo"),
    ]
    # Future mtime to guarantee stale.
    import time
    fake_project["set_olean_mtime"]("Proj.Foo", time.time() + 100)

    with patch.object(exp, "run_lean_export", stub):
        result = exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # Two subprocess calls total: initial full + partial.
    assert len(calls) == 2
    # The partial call had a filter of just Proj.Foo.
    assert calls[1]["modules"] == ["Proj.Foo"]
    # Result has the new decls plus the untouched Proj.Sub.Bar decl.
    names = sorted(d["name"] for d in result["declarations"])
    assert names == ["Proj.Foo.a_renamed", "Proj.Foo.new_decl", "Proj.Sub.Bar.b"]


def test_module_deletion_drops_decls_without_subprocess(fake_project) -> None:
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # Delete the olean for Proj.Sub.Bar.
    (fake_project["olean_root"] / "Sub" / "Bar.olean").unlink()

    with patch.object(exp, "run_lean_export", stub):
        result = exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # No subprocess for the delete-only case (nothing to_export, just to_delete).
    assert len(calls) == 1
    assert [d["name"] for d in result["declarations"]] == ["Proj.Foo.a"]
    assert "Proj.Sub.Bar" not in result["module_mtimes"]


def test_exporter_change_triggers_full_rebuild(fake_project) -> None:
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # Touch the exporter script in the future.
    import os, time
    future = time.time() + 100
    os.utime(fake_project["export_lean"], (future, future))

    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # Two full exports: initial + post-exporter-change.
    assert len(calls) == 2
    assert calls[0]["modules"] is None
    assert calls[1]["modules"] is None  # full rebuild


def test_force_full_bypasses_cache(fake_project) -> None:
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )
        # No changes, but force_full=True → should run full export again.
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
            force_full=True,
        )

    assert len(calls) == 2
    assert calls[1]["modules"] is None


def test_ghost_module_garbage_collected_when_canonical_set_shrinks(fake_project) -> None:
    """Regression: Lake leaves stale oleans on disk after an import is removed.
    The disk walk sees them; the exporter's project_modules does not. The cache
    must drop them on the next partial export.
    """
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []

    # Round 1: full cache with both modules present and reachable.
    stub_full = _stub_run_lean_export_factory(decls_by_mod, calls)
    with patch.object(exp, "run_lean_export", stub_full):
        exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    cache_after_full = json.loads(fake_project["cache_path"].read_text())
    assert set(cache_after_full["module_mtimes"].keys()) == {"Proj.Foo", "Proj.Sub.Bar"}

    # Round 2: simulate "import removed" — Proj.Sub.Bar.olean still on disk
    # (unchanged), but the exporter's project_modules now only reports Proj.Foo
    # (Bar is no longer reachable). Bump Proj.Foo's olean to force a partial.
    import time
    fake_project["set_olean_mtime"]("Proj.Foo", time.time() + 100)

    stub_after_removal = _stub_run_lean_export_factory(
        decls_by_mod, calls,
        project_modules=["Proj.Foo"],  # Bar gone from canonical set
    )
    with patch.object(exp, "run_lean_export", stub_after_removal):
        result = exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # Ghost Proj.Sub.Bar must be evicted from the cache despite its olean
    # still being on disk and despite no explicit deletion signal from oleans.
    assert set(result["module_mtimes"].keys()) == {"Proj.Foo"}, \
        f"ghost not GC'd: {result['module_mtimes']}"
    names = sorted(d["name"] for d in result["declarations"])
    assert names == ["Proj.Foo.a"], f"stale decl(s) survived: {names}"


def test_partial_without_project_modules_does_not_drop_cached_modules(fake_project) -> None:
    """Defensive: if the exporter (e.g. an older version) doesn't return
    ``project_modules``, we must NOT GC anything based on the absent signal.
    """
    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    # Prime
    with patch.object(exp, "run_lean_export", stub):
        exp.export_cached(
            fake_project["lake_root"], fake_project["root_module"],
            fake_project["cache_path"], fake_project["export_lean"],
        )

    # Now stub that omits project_modules entirely (old exporter)
    def old_stub(lake_root, root_module, export_lean, timeout=None, modules=None):
        modules_list = sorted(modules) if modules is not None else None
        calls.append({"modules": modules_list})
        if modules_list is None:
            decls = [d for v in decls_by_mod.values() for d in v]
        else:
            decls = [d for m in modules_list for d in decls_by_mod.get(m, [])]
        return {"root_module": root_module, "declaration_count": len(decls), "declarations": decls}

    import time
    fake_project["set_olean_mtime"]("Proj.Foo", time.time() + 200)

    with patch.object(exp, "run_lean_export", old_stub):
        result = exp.export_cached(
            fake_project["lake_root"], fake_project["root_module"],
            fake_project["cache_path"], fake_project["export_lean"],
        )

    # Both modules survive — we can't GC without canonical info
    assert set(result["module_mtimes"].keys()) == {"Proj.Foo", "Proj.Sub.Bar"}


def test_v1_cache_is_ignored_and_replaced(fake_project) -> None:
    # Write a v1-shaped cache (no schema_version) to disk.
    v1_cache = {
        "root_module": fake_project["root_module"],
        "declaration_count": 1,
        "declarations": [_decl("Proj.LegacyOnly.a", "Proj.LegacyOnly")],
    }
    fake_project["cache_path"].parent.mkdir(parents=True, exist_ok=True)
    fake_project["cache_path"].write_text(json.dumps(v1_cache))

    decls_by_mod = {
        "Proj.Foo": [_decl("Proj.Foo.a", "Proj.Foo")],
        "Proj.Sub.Bar": [_decl("Proj.Sub.Bar.b", "Proj.Sub.Bar")],
    }
    calls: list[dict[str, Any]] = []
    stub = _stub_run_lean_export_factory(decls_by_mod, calls)

    with patch.object(exp, "run_lean_export", stub):
        result = exp.export_cached(
            fake_project["lake_root"],
            fake_project["root_module"],
            fake_project["cache_path"],
            fake_project["export_lean"],
        )

    # v1 cache ignored → full rebuild, new v2 cache on disk.
    assert len(calls) == 1
    assert calls[0]["modules"] is None
    on_disk = json.loads(fake_project["cache_path"].read_text())
    assert on_disk["schema_version"] == exp.SCHEMA_VERSION
    # Result reflects the new exporter, not the legacy decl.
    assert sorted(d["name"] for d in result["declarations"]) == [
        "Proj.Foo.a",
        "Proj.Sub.Bar.b",
    ]
