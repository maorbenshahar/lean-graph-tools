"""Tests for sig tracker module."""

from lean_tree.sig.tracker import build_index, dep_closure
from lean_tree.common import find_decl, find_by_module


SAMPLE_DATA = {
    "root_module": "TestLib",
    "declaration_count": 4,
    "declarations": [
        {
            "name": "TestLib.MState",
            "kind": "structure",
            "module": "TestLib.Basic",
            "is_private": False,
            "type_signature": "Type",
            "deps": ["TestLib.Matrix"],
            "fields": [
                {"name": "val", "type": "Matrix n n \u2102", "projName": "TestLib.MState.val", "fromParent": False},
                {"name": "pos", "type": "val.PosSemidef", "projName": "TestLib.MState.pos", "fromParent": False},
            ],
            "line": 10,
        },
        {
            "name": "TestLib.Matrix",
            "kind": "structure",
            "module": "TestLib.Basic",
            "is_private": False,
            "type_signature": "\u2115 \u2192 \u2115 \u2192 Type \u2192 Type",
            "deps": [],
            "fields": [
                {"name": "data", "type": "Fin m \u2192 Fin n \u2192 \u03b1", "projName": "TestLib.Matrix.data"},
            ],
            "line": 5,
        },
        {
            "name": "TestLib.entropy",
            "kind": "def",
            "module": "TestLib.Entropy",
            "is_private": False,
            "type_signature": "TestLib.MState n \u2192 \u211d",
            "deps": ["TestLib.MState"],
            "line": 20,
        },
        {
            "name": "TestLib.entropy_nonneg",
            "kind": "theorem",
            "module": "TestLib.Entropy",
            "is_private": False,
            "type_signature": "\u2200 (\u03c1 : TestLib.MState n), TestLib.entropy \u03c1 \u2265 0",
            "deps": ["TestLib.MState", "TestLib.entropy"],
            "line": 30,
        },
    ],
}


def test_build_index():
    index = build_index(SAMPLE_DATA)
    assert len(index) == 4
    assert "TestLib.MState" in index
    assert index["TestLib.MState"].fields is not None
    assert len(index["TestLib.MState"].fields) == 2


def test_find_decl_exact():
    index = build_index(SAMPLE_DATA)
    found = find_decl(index, "TestLib.entropy")
    assert len(found) == 1
    assert found[0].name == "TestLib.entropy"


def test_find_decl_suffix():
    index = build_index(SAMPLE_DATA)
    found = find_decl(index, "entropy")
    assert len(found) == 1
    assert found[0].name == "TestLib.entropy"


def test_find_by_module():
    index = build_index(SAMPLE_DATA)
    found = find_by_module(index, "Entropy", root_module="TestLib")
    assert len(found) == 2  # entropy + entropy_nonneg


def test_dep_closure():
    index = build_index(SAMPLE_DATA)
    closure = dep_closure(index, ["TestLib.entropy_nonneg"])
    names = [d.name for d in closure]
    # Should include the theorem, its deps (MState, entropy), and MState's dep (Matrix)
    assert "TestLib.entropy_nonneg" in names
    assert "TestLib.MState" in names
    assert "TestLib.entropy" in names
    assert "TestLib.Matrix" in names


def test_dep_closure_no_duplicates():
    index = build_index(SAMPLE_DATA)
    closure = dep_closure(index, ["TestLib.entropy_nonneg"])
    names = [d.name for d in closure]
    assert len(names) == len(set(names))
