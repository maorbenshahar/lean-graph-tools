"""Tests for shared CLI helpers."""

import argparse

import pytest

from lean_graph.common import add_export_timeout_arg, export_timeout_from_args


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    add_export_timeout_arg(parser)
    return parser


def test_export_timeout_default_is_none() -> None:
    parser = _parser()
    args = parser.parse_args([])
    assert export_timeout_from_args(args, parser) is None


def test_export_timeout_zero_disables() -> None:
    parser = _parser()
    args = parser.parse_args(["--timeout", "0"])
    assert export_timeout_from_args(args, parser) is None


def test_export_timeout_positive_value() -> None:
    parser = _parser()
    args = parser.parse_args(["--timeout", "42.5"])
    assert export_timeout_from_args(args, parser) == 42.5


def test_export_timeout_negative_rejected() -> None:
    parser = _parser()
    args = parser.parse_args(["--timeout", "-1"])
    with pytest.raises(SystemExit):
        export_timeout_from_args(args, parser)
