"""
Tests for filtering nogoods (domain reductions / keep predicates).
"""
import cpmpy as cp

from proof2seq.pipeline import is_domain_reduction
from proof2seq.utils import get_variables
from tests.helpers import unsat_alldiff_model, solve_and_parse, cleanup, keep_unit, keep_all


def test_filter_by_unit_condition():
    model, _ = unsat_alldiff_model()
    _, nogoods, path = solve_and_parse(model, keep_step=keep_all)
    try:
        unit = [ng for ng in nogoods if keep_unit(ng)]
        assert all(len(get_variables(e)) <= 1 for e in unit)
        assert len(unit) <= len(nogoods)
    finally:
        cleanup(path)


def test_is_domain_reduction():
    x, y = cp.intvar(0, 1, shape=2, name=("x", "y"))
    assert is_domain_reduction(x == 1)
    assert is_domain_reduction(cp.BoolVal(False))
    assert not is_domain_reduction((x != 1) | (y != 1))


def test_filter_empty():
    assert [ng for ng in [] if keep_all(ng)] == []
