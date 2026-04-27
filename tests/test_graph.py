"""Tests for shared declaration graph searches."""

from dataclasses import dataclass

from lean_tree.graph import DeclarationGraph


@dataclass
class Node:
    name: str
    deps: list[str]


def test_closure_supports_multiple_roots_and_cycles():
    graph = DeclarationGraph({
        "A": Node("A", ["B"]),
        "B": Node("B", ["C"]),
        "C": Node("C", ["A"]),
        "D": Node("D", ["B"]),
        "E": Node("E", []),
    })

    reachable = graph.closure(["A", "E"], "dependencies", include_roots=True)
    assert [(node.name, node.distance) for node in reachable] == [
        ("A", 0),
        ("E", 0),
        ("B", 1),
        ("C", 2),
    ]


def test_reverse_closure_finds_dependents():
    graph = DeclarationGraph({
        "A": Node("A", []),
        "B": Node("B", ["A"]),
        "C": Node("C", ["B"]),
        "D": Node("D", ["A"]),
    })

    reachable = graph.closure(["A"], "dependents")
    assert [(node.name, node.distance) for node in reachable] == [
        ("B", 1),
        ("D", 1),
        ("C", 2),
    ]


def test_reverse_edges_are_lazy():
    graph = DeclarationGraph({
        "A": Node("A", []),
        "B": Node("B", ["A"]),
    })

    graph.closure_names(["B"], "dependencies", include_roots=True)
    assert graph._reverse is None

    assert graph.neighbors("A", "dependents") == ["B"]
    assert graph._reverse is not None


def test_shortest_path():
    graph = DeclarationGraph({
        "A": Node("A", ["B", "C"]),
        "B": Node("B", ["D"]),
        "C": Node("C", ["D"]),
        "D": Node("D", []),
    })

    assert graph.shortest_path("A", "D") == ["A", "B", "D"]
