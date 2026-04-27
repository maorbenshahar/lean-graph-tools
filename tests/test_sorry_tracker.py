"""Tests for sorry dependency tracking over the shared graph core."""

from lean_tree.sorry.tracker import (
    analyze_scope,
    analyze_target,
    build_index,
    has_transitive_sorry,
    transitive_deps,
)


SAMPLE_DATA = {
    "root_module": "TestLib",
    "declaration_count": 7,
    "declarations": [
        {
            "name": "TestLib.clean",
            "kind": "def",
            "module": "TestLib.Basic",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": [],
            "line": 1,
        },
        {
            "name": "TestLib.sorryLeaf",
            "kind": "theorem",
            "module": "TestLib.Basic",
            "has_sorry": True,
            "contains_sorry": True,
            "is_private": False,
            "deps": [],
            "line": 5,
        },
        {
            "name": "TestLib.mid",
            "kind": "def",
            "module": "TestLib.Middle",
            "has_sorry": True,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.sorryLeaf"],
            "line": 8,
        },
        {
            "name": "TestLib.top",
            "kind": "theorem",
            "module": "TestLib.Top",
            "has_sorry": True,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.mid", "TestLib.clean"],
            "line": 10,
        },
        {
            "name": "TestLib.cycleA",
            "kind": "def",
            "module": "TestLib.Cycle",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.cycleB"],
            "line": 3,
        },
        {
            "name": "TestLib.cycleB",
            "kind": "def",
            "module": "TestLib.Cycle",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.cycleA"],
            "line": 4,
        },
        {
            "name": "TestLib.assumed",
            "kind": "axiom",
            "module": "TestLib.Basic",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": [],
            "line": 20,
        },
    ],
}


def test_transitive_deps_uses_graph_and_handles_cycles():
    index = build_index(SAMPLE_DATA)
    closure = transitive_deps(index, "TestLib.cycleA")
    assert [decl.name for decl in closure] == [
        "TestLib.cycleA",
        "TestLib.cycleB",
    ]


def test_has_transitive_sorry():
    index = build_index(SAMPLE_DATA)
    assert has_transitive_sorry("TestLib.top", index)
    assert not has_transitive_sorry("TestLib.clean", index)
    assert has_transitive_sorry("TestLib.assumed", index)


def test_analyze_target_finds_sorry_leaf_and_tree():
    index = build_index(SAMPLE_DATA)
    result = analyze_target(index, "TestLib.top", show_tree=True, lake_root="/tmp")
    assert result.total_deps == 4
    assert [leaf.name for leaf in result.sorry_leaves] == ["TestLib.sorryLeaf"]
    assert result.sorry_leaves[0].file == "/tmp/TestLib/Basic.lean"
    assert "TestLib.mid" in result.tree
    assert "TestLib.sorryLeaf [sorry]" in result.tree


def test_analyze_scope_deduplicates_shared_sorry_leaf():
    index = build_index(SAMPLE_DATA)
    result = analyze_scope(index, [index["TestLib.mid"], index["TestLib.top"]])
    assert [leaf.name for leaf in result.sorry_leaves] == ["TestLib.sorryLeaf"]
    assert result.total_deps == 4
