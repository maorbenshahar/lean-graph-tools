from lean_tree.export import EXPORT_DECLS_LEAN, EXPORT_SIGS_LEAN


def test_export_assets_exist() -> None:
    assert EXPORT_DECLS_LEAN.exists()
    assert EXPORT_SIGS_LEAN.exists()
