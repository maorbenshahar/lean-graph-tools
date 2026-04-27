"""Tests for downstream dependency tracking."""

from lean_tree.downstream.tracker import (
    analyze_downstream,
    analyze_upstream,
    build_index,
    build_reverse_index,
    dependency_relation,
    downstream_closure,
    find_dependency_path,
    render_dependency_tree,
    render_downstream_tree,
    upstream_closure,
)


SAMPLE_DATA = {
    "root_module": "TestLib",
    "declaration_count": 7,
    "declarations": [
        {
            "name": "TestLib.BaseType",
            "kind": "inductive",
            "module": "TestLib.Basic",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": [],
            "line": 3,
        },
        {
            "name": "TestLib.mkBase",
            "kind": "def",
            "module": "TestLib.Basic",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.BaseType"],
            "line": 8,
        },
        {
            "name": "TestLib.baseLemma",
            "kind": "theorem",
            "module": "TestLib.Basic",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.mkBase", "TestLib.BaseType"],
            "line": 12,
        },
        {
            "name": "TestLib.midDef",
            "kind": "def",
            "module": "TestLib.Middle",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.baseLemma"],
            "line": 5,
        },
        {
            "name": "TestLib.topTheorem",
            "kind": "theorem",
            "module": "TestLib.Top",
            "has_sorry": True,
            "contains_sorry": True,
            "is_private": False,
            "deps": ["TestLib.midDef"],
            "line": 9,
        },
        {
            "name": "TestLib.sideTheorem",
            "kind": "theorem",
            "module": "TestLib.Top",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": ["TestLib.BaseType"],
            "line": 15,
        },
        {
            "name": "TestLib.unrelated",
            "kind": "def",
            "module": "TestLib.Other",
            "has_sorry": False,
            "contains_sorry": False,
            "is_private": False,
            "deps": [],
            "line": 2,
        },
    ],
}


def test_build_reverse_index():
    index = build_index(SAMPLE_DATA)
    reverse = build_reverse_index(index)
    assert reverse["TestLib.BaseType"] == [
        "TestLib.mkBase",
        "TestLib.baseLemma",
        "TestLib.sideTheorem",
    ]


def test_downstream_closure_includes_all_kinds():
    index = build_index(SAMPLE_DATA)
    nodes = downstream_closure(index, "TestLib.BaseType")
    names = [node.decl.name for node in nodes]
    assert "TestLib.mkBase" in names
    assert "TestLib.baseLemma" in names
    assert "TestLib.midDef" in names
    assert "TestLib.topTheorem" in names
    assert "TestLib.sideTheorem" in names
    assert "TestLib.unrelated" not in names


def test_downstream_closure_tracks_distance():
    index = build_index(SAMPLE_DATA)
    nodes = downstream_closure(index, "TestLib.BaseType")
    distances = {node.decl.name: node.distance for node in nodes}
    assert distances["TestLib.mkBase"] == 1
    assert distances["TestLib.baseLemma"] == 1
    assert distances["TestLib.midDef"] == 2
    assert distances["TestLib.topTheorem"] == 3


def test_upstream_closure_includes_all_kinds():
    index = build_index(SAMPLE_DATA)
    nodes = upstream_closure(index, "TestLib.topTheorem")
    assert [(node.decl.name, node.distance) for node in nodes] == [
        ("TestLib.midDef", 1),
        ("TestLib.baseLemma", 2),
        ("TestLib.mkBase", 3),
        ("TestLib.BaseType", 3),
    ]


def test_upstream_direct_limit():
    index = build_index(SAMPLE_DATA)
    nodes = upstream_closure(index, "TestLib.baseLemma", max_depth=1)
    assert {node.decl.name for node in nodes} == {
        "TestLib.mkBase",
        "TestLib.BaseType",
    }


def test_downstream_direct_limit():
    index = build_index(SAMPLE_DATA)
    nodes = downstream_closure(index, "TestLib.BaseType", max_depth=1)
    assert {node.decl.name for node in nodes} == {
        "TestLib.mkBase",
        "TestLib.baseLemma",
        "TestLib.sideTheorem",
    }


def test_analyze_downstream_renders_tree():
    index = build_index(SAMPLE_DATA)
    result = analyze_downstream(index, "TestLib.BaseType", show_tree=True)
    assert result.total_downstream == 5
    assert "TestLib.BaseType" in result.tree
    assert "TestLib.topTheorem" in result.tree
    assert "contains sorry" in result.tree


def test_analyze_upstream_renders_tree():
    index = build_index(SAMPLE_DATA)
    result = analyze_upstream(index, "TestLib.topTheorem", show_tree=True)
    assert result.total_upstream == 4
    assert "TestLib.topTheorem" in result.tree
    assert "TestLib.BaseType" in result.tree


def test_render_downstream_tree_shared_node():
    index = build_index(SAMPLE_DATA)
    tree = render_downstream_tree(index, "TestLib.BaseType")
    assert "TestLib.baseLemma (see above)" in tree


def test_render_upstream_tree_diamond_does_not_duplicate_subtree():
    data = {
        "declarations": [
            {
                "name": "A", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["B", "C"],
            },
            {
                "name": "B", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["D"],
            },
            {
                "name": "C", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["D"],
            },
            {
                "name": "D", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": [],
            },
        ],
    }
    index = build_index(data)

    tree = render_dependency_tree(index, "A", "dependencies")
    assert tree.count("D [def]") == 1
    assert "D (see above)" in tree


def test_render_downstream_tree_diamond_does_not_duplicate_subtree():
    data = {
        "declarations": [
            {
                "name": "A", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["B", "C"],
            },
            {
                "name": "B", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["D"],
            },
            {
                "name": "C", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["D"],
            },
            {
                "name": "D", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": [],
            },
        ],
    }
    index = build_index(data)

    tree = render_dependency_tree(index, "D", "dependents")
    assert tree.count("A [def]") == 1
    assert "A (see above)" in tree


def test_render_tree_cycle_terminates_with_see_above():
    data = {
        "declarations": [
            {
                "name": "A", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["B"],
            },
            {
                "name": "B", "kind": "def", "module": "M",
                "has_sorry": False, "contains_sorry": False,
                "is_private": False, "deps": ["A"],
            },
        ],
    }
    index = build_index(data)

    tree = render_dependency_tree(index, "A", "dependencies")
    assert tree.count("A [def]") == 1
    assert "A (see above)" in tree


def test_find_dependency_path():
    index = build_index(SAMPLE_DATA)
    path = find_dependency_path(index, "TestLib.topTheorem", "TestLib.BaseType")
    assert path == [
        "TestLib.topTheorem",
        "TestLib.midDef",
        "TestLib.baseLemma",
        "TestLib.BaseType",
    ]


def test_dependency_relation_checks_both_directions():
    index = build_index(SAMPLE_DATA)
    result = dependency_relation(index, "TestLib.BaseType", "TestLib.topTheorem")
    assert not result.left_depends_on_right
    assert result.right_depends_on_left
    assert result.right_to_left_path == [
        "TestLib.topTheorem",
        "TestLib.midDef",
        "TestLib.baseLemma",
        "TestLib.BaseType",
    ]
