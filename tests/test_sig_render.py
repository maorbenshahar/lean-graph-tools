"""Tests for sig render module."""

from lean_graph.sig.tracker import build_index, dep_closure, DeclInfo, FieldInfo, CtorInfo
from lean_graph.sig.render import render_decl, render_context


def test_render_theorem():
    decl = DeclInfo(
        name="Foo.bar", kind="theorem", module="Foo",
        is_private=False, type_signature="\u2200 x, x = x", deps=[],
    )
    result = render_decl(decl)
    assert "theorem Foo.bar" in result
    assert "\u2200 x, x = x" in result


def test_render_structure():
    decl = DeclInfo(
        name="Foo.MyStruct", kind="structure", module="Foo",
        is_private=False, type_signature="Type",
        deps=[],
        fields=[
            FieldInfo(name="x", type="\u2115"),
            FieldInfo(name="h", type="x > 0"),
        ],
    )
    result = render_decl(decl)
    assert "structure Foo.MyStruct where" in result
    assert "x : \u2115" in result
    assert "h : x > 0" in result


def test_render_structure_extends():
    """Structure with parents should show extends and skip parent fields."""
    decl = DeclInfo(
        name="Foo.DensityOp", kind="structure", module="Foo",
        is_private=False, type_signature="Nat \u2192 Type",
        deps=["Foo.PosSemidefOp"],
        fields=[
            FieldInfo(name="toPosSemidefOp", type="...", from_parent=True),
            FieldInfo(name="trace_one", type="toOp.trace = 1"),
        ],
        parents=["Foo.PosSemidefOp"],
    )
    result = render_decl(decl)
    assert "extends PosSemidefOp" in result
    assert "Nat \u2192 Type" in result
    assert "trace_one" in result
    # Parent field should NOT be shown
    assert "toPosSemidefOp" not in result


def test_render_structure_extends_multiple():
    """Structure extending multiple parents."""
    decl = DeclInfo(
        name="Foo.Bar", kind="structure", module="Foo",
        is_private=False, type_signature="Type",
        deps=[],
        fields=[
            FieldInfo(name="toA", type="...", from_parent=True),
            FieldInfo(name="toB", type="...", from_parent=True),
            FieldInfo(name="myField", type="\u2115"),
        ],
        parents=["Foo.A", "Foo.B"],
    )
    result = render_decl(decl)
    assert "extends A, B" in result
    assert "myField : \u2115" in result
    assert "toA" not in result
    assert "toB" not in result


def test_render_inductive():
    decl = DeclInfo(
        name="Foo.MyInd", kind="inductive", module="Foo",
        is_private=False, type_signature="Type \u2192 Type",
        deps=[],
        constructors=[
            CtorInfo(name="nil", type="Foo.MyInd \u03b1"),
            CtorInfo(name="cons", type="\u03b1 \u2192 Foo.MyInd \u03b1 \u2192 Foo.MyInd \u03b1"),
        ],
    )
    result = render_decl(decl)
    assert "inductive Foo.MyInd" in result
    assert "| nil" in result
    assert "| cons" in result


def test_render_abbrev():
    decl = DeclInfo(
        name="Foo.myAbbrev", kind="abbrev", module="Foo",
        is_private=False, type_signature="Type",
        deps=[], value="Nat",
    )
    result = render_decl(decl)
    assert "abbrev Foo.myAbbrev" in result
    assert "Nat" in result


def test_render_context_groups_by_module():
    targets = [
        DeclInfo(name="A.foo", kind="def", module="A",
                 is_private=False, type_signature="B.Bar \u2192 \u2115", deps=["B.Bar"]),
    ]
    context = targets + [
        DeclInfo(name="B.Bar", kind="structure", module="B",
                 is_private=False, type_signature="Type", deps=[],
                 fields=[FieldInfo(name="x", type="\u2115")]),
    ]
    result = render_context(targets, context, root_module="Root", header="test")
    assert "Target declarations" in result
    assert "Required context" in result
    assert "def A.foo" in result
    assert "structure B.Bar" in result


def test_render_context_filters_projections():
    """Standalone projection declarations should be filtered when struct is present."""
    targets = [
        DeclInfo(name="A.foo", kind="def", module="A",
                 is_private=False, type_signature="B.Bar \u2192 \u2115",
                 deps=["B.Bar", "B.Bar.x"]),
    ]
    bar_struct = DeclInfo(
        name="B.Bar", kind="structure", module="B",
        is_private=False, type_signature="Type", deps=[],
        fields=[FieldInfo(name="x", type="\u2115", proj_name="B.Bar.x")],
    )
    bar_proj = DeclInfo(
        name="B.Bar.x", kind="abbrev", module="B",
        is_private=False, type_signature="B.Bar \u2192 \u2115", deps=["B.Bar"],
        value="fun self => self.1",
    )
    context = targets + [bar_struct, bar_proj]
    result = render_context(targets, context, root_module="Root", header="test")
    # The structure should appear
    assert "structure B.Bar" in result
    # The standalone projection should NOT appear
    assert "abbrev B.Bar.x" not in result


def test_render_class():
    """Class declarations should render with 'class' keyword."""
    decl = DeclInfo(
        name="Foo.MyClass", kind="class", module="Foo",
        is_private=False, type_signature="Type \u2192 Type",
        deps=[],
        fields=[FieldInfo(name="op", type="\u03b1 \u2192 \u03b1")],
    )
    result = render_decl(decl)
    assert "class Foo.MyClass" in result
    assert "op : \u03b1 \u2192 \u03b1" in result


def test_render_sorry_warning():
    """Declarations with sorry should show a warning."""
    decl = DeclInfo(
        name="Foo.bar", kind="theorem", module="Foo",
        is_private=False, type_signature="\u2200 x, x = x", deps=[],
        has_sorry=True,
    )
    result = render_decl(decl)
    assert "sorry" in result.lower()
    assert "WARNING" in result or "\u26a0" in result


def test_render_no_sorry_warning():
    """Declarations without sorry should not show a warning."""
    decl = DeclInfo(
        name="Foo.bar", kind="theorem", module="Foo",
        is_private=False, type_signature="\u2200 x, x = x", deps=[],
        has_sorry=False,
    )
    result = render_decl(decl)
    assert "sorry" not in result.lower()


def test_render_context_leaves_first():
    """Leaf dependencies should appear before intermediate ones (reversed BFS)."""
    targets = [
        DeclInfo(name="A.top", kind="def", module="A",
                 is_private=False, type_signature="B.Mid \u2192 \u2115", deps=["B.Mid"]),
    ]
    mid = DeclInfo(name="B.Mid", kind="structure", module="B",
                   is_private=False, type_signature="Type", deps=["C.Leaf"],
                   fields=[FieldInfo(name="x", type="C.Leaf")])
    leaf = DeclInfo(name="C.Leaf", kind="structure", module="C",
                    is_private=False, type_signature="Type", deps=[],
                    fields=[FieldInfo(name="v", type="\u2115")])
    # BFS order: Mid, Leaf. Reversed: Leaf, Mid.
    context = targets + [mid, leaf]
    result = render_context(targets, context, root_module="Root", header="test")
    # Check within the context section only (after "Required context")
    ctx_section = result[result.index("Required context"):]
    leaf_pos = ctx_section.index("structure C.Leaf")
    mid_pos = ctx_section.index("structure B.Mid")
    assert leaf_pos < mid_pos, "Leaf dependencies should appear before intermediate ones"
