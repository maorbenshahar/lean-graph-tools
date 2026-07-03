"""Tests for the source-faithful audit-digest renderer (sig.render).

The legacy pretty-printed `render_decl`/`render_context` path was removed (the
exporter no longer emits `type_signature`/`value`/`fields[].type`/`constructors`).
These tests exercise the live digest renderers, which build from the verbatim
`source_text` slice.
"""

from lean_graph.sig.tracker import DeclInfo, FieldInfo
from lean_graph.sig.render import (
    _apply_elision,
    _atom_used_as_binder,
    _projection_names,
    _render_decl_source,
    render_digest,
)


def _decl(name, kind, module, *, deps=None, source_text=None, byTactic_ranges=None,
          decl_namespace="", line=1, docstring=None, is_private=False, fields=None):
    return DeclInfo(
        name=name, kind=kind, module=module, is_private=is_private,
        deps=deps or [], line=line, source_text=source_text,
        byTactic_ranges=byTactic_ranges, decl_namespace=decl_namespace,
        docstring=docstring, fields=fields,
    )


def test_apply_elision_splices_token_over_by_block():
    src = "theorem foo : True := by trivial"
    start = src.encode().index(b"by trivial")
    decl = _decl("Foo.foo", "theorem", "Foo", source_text=src,
                 byTactic_ranges=[[start, len(src.encode())]])
    assert _apply_elision(decl, "sorry") == "theorem foo : True := sorry"


def test_apply_elision_no_ranges_returns_source_unchanged():
    decl = _decl("Foo.d", "def", "Foo", source_text="def d := 5", byTactic_ranges=[])
    assert _apply_elision(decl, "sorry") == "def d := 5"


def test_apply_elision_handles_unicode_byte_offsets():
    # Byte offsets, not character offsets: the proof block follows a multibyte ‖.
    src = "theorem n : ‖x‖ = 0 := by simp"
    b = src.encode("utf-8")
    start = b.index(b"by simp")
    decl = _decl("Foo.n", "theorem", "Foo", source_text=src,
                 byTactic_ranges=[[start, len(b)]])
    assert _apply_elision(decl, "sorry") == "theorem n : ‖x‖ = 0 := sorry"


def test_render_decl_source_uses_slice():
    decl = _decl("Foo.d", "def", "Foo", source_text="def d : Nat := 5")
    assert _render_decl_source(decl) == "def d : Nat := 5"


def test_render_decl_source_placeholder_when_no_slice():
    out = _render_decl_source(_decl("Foo.d", "def", "Foo", source_text=None))
    assert "no source slice" in out
    assert "Foo.d" in out


def test_projection_names_collects_proj_names():
    struct = _decl("Foo.S", "structure", "Foo",
                   fields=[FieldInfo(name="x", proj_name="Foo.S.x"),
                           FieldInfo(name="y", proj_name="Foo.S.y")])
    assert _projection_names([struct]) == {"Foo.S.x", "Foo.S.y"}


def test_render_digest_print_imports_and_checks():
    leaf = _decl("Foo.leaf", "def", "Foo.Basic", source_text="def leaf : Nat := 0")
    thm = _decl("Foo.thm", "theorem", "Foo.Main", deps=["Foo.leaf"],
                source_text="theorem thm : Foo.leaf = 0 := by sorry")
    index = {d.name: d for d in (leaf, thm)}
    out = render_digest([thm], [thm, leaf], index, root_module="Foo",
                        module_imports={}, project_modules={"Foo.Basic", "Foo.Main"},
                        mode="print")
    assert "import Foo.Basic" in out
    assert "import Foo.Main" in out
    assert "#check @Foo.thm" in out      # theorem -> #check (statement)
    assert "#print Foo.leaf" in out      # small non-recursive def -> #print
    assert "TARGET" in out               # the target theorem is tagged


def test_render_digest_self_contained_imports_mathlib_and_sorries_proofs():
    leaf = _decl("Foo.leaf", "def", "Foo.Basic", source_text="def leaf : Nat := 0",
                 decl_namespace="Foo")
    thm = _decl("Foo.thm", "theorem", "Foo.Main", deps=["Foo.leaf"],
                source_text="theorem thm : Foo.leaf = 0 := by sorry",
                decl_namespace="Foo")
    index = {d.name: d for d in (leaf, thm)}
    out = render_digest(
        [thm], [thm, leaf], index, root_module="Foo",
        module_imports={"Foo.Basic": [], "Foo.Main": ["Foo.Basic"]},
        project_modules={"Foo.Basic", "Foo.Main"},
        mode="self_contained",
    )
    assert "import Mathlib" in out
    assert "def leaf : Nat := 0" in out  # leaf re-declared verbatim
    assert "namespace Foo" in out        # placed under its real namespace
    assert "sorry" in out                # the theorem body is sorried


def test_atom_used_as_binder_flags_only_binder_positions():
    # Identifier-word atoms in binder positions (parenthesized, instance-bracket,
    # ∀/∃/fun) would shadow the binder once re-declared as notation.
    assert _atom_used_as_binder("X", "def f (X : Op n) : Op n := X")
    assert _atom_used_as_binder("X", "theorem t : ∃ X : Op n, P X := by sorry")
    assert _atom_used_as_binder("Z", "structure H (S X Z : Type*) where")
    assert _atom_used_as_binder("Y", "def g := fun Y => Y + 1")
    # Symbolic atoms can never collide with a binder.
    assert not _atom_used_as_binder("⊗", "def f := a ⊗ b")
    assert not _atom_used_as_binder("|0⟩", "def f := |0⟩")
    # A term-only occurrence is not a binder.
    assert not _atom_used_as_binder("X", "def f := gateI * X")


def test_self_contained_drops_binder_colliding_notation():
    # `notation "X" => pauliX` from one module would, in the flattened file, shadow
    # the `(X : Op 2)` binder in another module and break parsing. It is dropped,
    # while a symbolic notation that cannot collide is kept.
    gate = _decl("Q.pauliX", "def", "Q.Gates",
                 source_text="def pauliX : Op 2 := 0", decl_namespace="Q")
    user = _decl("Q.f", "def", "Q.Main", deps=["Q.pauliX"],
                 source_text="def f (X : Op 2) : Op 2 := X ⊗ X", decl_namespace="Q")
    index = {d.name: d for d in (gate, user)}
    out = render_digest(
        [user], [user, gate], index, root_module="Q",
        module_imports={"Q.Gates": [], "Q.Main": ["Q.Gates"]},
        project_modules={"Q.Gates", "Q.Main"},
        module_notations={"Q.Gates": [
            {"text": 'notation "X" => pauliX', "line": 5,
             "tokens": ["X"], "rhs_idents": ["pauliX"]},
            {"text": 'infixl:70 " ⊗ " => tensor', "line": 6,
             "tokens": ["⊗"], "rhs_idents": ["tensor"]},
        ]},
        mode="self_contained",
    )
    assert 'notation "X"' not in out       # binder-colliding word notation -> dropped
    assert "⊗" in out                       # symbolic notation -> kept


def test_self_contained_recovers_prop_erased_proof_helper():
    # `f`'s body references lemma `aux` in a term position, but `aux` is prop-erased
    # from `f.deps`; the self-contained closure must still re-declare it or the
    # flattened file has an unknown identifier.
    aux = _decl("Q.aux", "theorem", "Q.Aux",
                source_text="theorem aux : True := by sorry", decl_namespace="Q")
    f = _decl("Q.f", "def", "Q.Main", deps=[],   # aux deliberately absent from deps
              source_text="def f : Nat := (aux).elim 0", decl_namespace="Q")
    index = {d.name: d for d in (aux, f)}
    out = render_digest(
        [f], [f], index, root_module="Q",
        module_imports={"Q.Aux": [], "Q.Main": ["Q.Aux"]},
        project_modules={"Q.Aux", "Q.Main"},
        mode="self_contained",
    )
    assert "theorem aux" in out            # recovered despite absence from `deps`
