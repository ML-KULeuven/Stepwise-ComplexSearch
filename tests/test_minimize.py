"""
Tests for proof2seq.minimize — global backwards MUS minimization over nogood lists.
"""
from proof2seq.minimize import minimize_proof
from proof2seq.pipeline import keep_user_var_nogoods
from proof2seq.utils import sanity_check_nogoods
from tests.helpers import (
    unsat_alldiff_model, unsat_sum_model, solve_and_parse, cleanup,
    MUS_SOLVER,
)


def test_minimize_reduces_or_keeps():
    model, (x, y) = unsat_alldiff_model()
    user_vars = frozenset([x, y])
    _, nogoods, path = solve_and_parse(model, keep_step=keep_user_var_nogoods(user_vars))
    try:
        minimized = minimize_proof(
            nogoods, model.constraints,
            mus_type="mus",
            mus_solver=MUS_SOLVER,
        )
        assert 0 < len(minimized) <= len(nogoods)
        sanity_check_nogoods(minimized, model.constraints)
    finally:
        cleanup(path)


def test_minimize_on_larger_proof():
    model, (x, y, z) = unsat_sum_model()
    user_vars = frozenset([x, y, z])
    _, nogoods, path = solve_and_parse(model, keep_step=keep_user_var_nogoods(user_vars))
    try:
        minimized = minimize_proof(
            nogoods, model.constraints,
            mus_type="mus",
            mus_solver=MUS_SOLVER,
        )
        assert 0 < len(minimized) <= len(nogoods)
        sanity_check_nogoods(minimized, model.constraints)
    finally:
        cleanup(path)


def test_minimize_empty():
    assert minimize_proof([], []) == []


def test_minimize_preserves_false():
    model, (x, y) = unsat_alldiff_model()
    user_vars = frozenset([x, y])
    _, nogoods, path = solve_and_parse(model, keep_step=keep_user_var_nogoods(user_vars))
    try:
        minimized = minimize_proof(
            nogoods, model.constraints,
            mus_type="mus",
            mus_solver=MUS_SOLVER,
        )
        assert any(str(ng) == "boolval(False)" for ng in minimized)
    finally:
        cleanup(path)
