"""
Tests for proof2seq.parsing — DRCP → list of nogood expressions.
"""
import cpmpy as cp
from cpmpy.expressions.core import BoolVal, Comparison, Operator

from proof2seq.utils import get_variables
from proof2seq.pipeline import keep_user_var_nogoods
from tests.helpers import (
    unsat_alldiff_model, solve_and_parse, cleanup,
    keep_unit, keep_all,
)


def test_name_to_var_map():
    model, (x, y) = unsat_alldiff_model()
    parser, nogoods, path = solve_and_parse(model)
    try:
        assert parser._name_to_var["x"] is x
        assert parser._name_to_var["y"] is y
        assert "x" in parser._varmap
        assert isinstance(next(iter(parser._varmap)), str)
    finally:
        cleanup(path)


def test_parse_returns_list_of_expressions():
    model, _ = unsat_alldiff_model()
    parser, nogoods, path = solve_and_parse(model)
    try:
        assert isinstance(nogoods, list)
        assert len(nogoods) > 0
        for ng in nogoods:
            assert isinstance(ng, (Comparison, Operator, BoolVal)), f"unexpected {type(ng)}: {ng}"
        assert any(isinstance(ng, BoolVal) and ng.value() is False for ng in nogoods)
    finally:
        cleanup(path)


def test_keep_step_filters():
    model, (x, y) = unsat_alldiff_model()
    user_vars = frozenset([x, y])

    parser, all_ng, path = solve_and_parse(model, keep_step=keep_all)
    try:
        filtered = parser.read_proof(keep_step=keep_user_var_nogoods(user_vars), prefix=path)
        unit = parser.read_proof(keep_step=keep_unit, prefix=path)

        assert len(filtered) <= len(all_ng)
        assert len(unit) <= len(filtered)
        for ng in filtered:
            assert frozenset(get_variables(ng)) <= user_vars
        for ng in unit:
            assert len(get_variables(ng)) <= 1
    finally:
        cleanup(path)


def test_deduplicates_expressions():
    model, _ = unsat_alldiff_model()
    _, nogoods, path = solve_and_parse(model, keep_step=keep_all)
    try:
        assert len(nogoods) == len(set(map(str, nogoods)))
    finally:
        cleanup(path)


def test_empty_nogood_concludes_unsat():
    model, _ = unsat_alldiff_model()
    _, nogoods, path = solve_and_parse(model)
    try:
        assert isinstance(nogoods[-1], BoolVal) and nogoods[-1].value() is False
        # no duplicate False at the end
        assert sum(isinstance(ng, BoolVal) and ng.value() is False for ng in nogoods) == 1
    finally:
        cleanup(path)


def test_propagation_and_nogood_lines_present():
    model, _ = unsat_alldiff_model()
    parser, nogoods, path = solve_and_parse(model, keep_step=keep_all)
    try:
        with open(path) as f:
            lines = f.readlines()
        assert any(l.startswith("i ") for l in lines)
        assert any(l.startswith("n ") for l in lines)
        assert len(nogoods) >= 1
    finally:
        cleanup(path)


def test_parse_one_lit_unknown_var_raises():
    model, _ = unsat_alldiff_model()
    parser, _, path = solve_and_parse(model)
    try:
        try:
            parser.parse_one_lit("[unknown_var == 1]")
            assert False, "expected ValueError"
        except ValueError:
            pass
    finally:
        cleanup(path)
