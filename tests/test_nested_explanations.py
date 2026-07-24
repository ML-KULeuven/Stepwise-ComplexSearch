"""
Tests for nested_explanations — nested step-wise explanations from proofs.
"""
import tempfile
import warnings

import cpmpy as cp

from nested_explanations import (
    find_explanation_sequence,
    get_first_decision_in_proof,
    get_nested_explanation_with_proof,
    more_than_one_constraint,
)
from tests.helpers import unsat_alldiff_model, MUS_SOLVER


def test_more_than_one_constraint():
    assert more_than_one_constraint(dict(constraints=[1, 2])) is True
    assert more_than_one_constraint(dict(constraints=[1])) is False
    assert more_than_one_constraint(dict(constraints=[])) is False


def test_get_first_decision_finds_candidate():
    x, y = cp.intvar(1, 2, shape=2, name=("x", "y"))
    step = dict(
        input_lits=[],
        constraints=[cp.AllDifferent([x, y]), x == 1, y == 1],
        output_lits=[cp.BoolVal(False)],
    )
    decision, opposed = get_first_decision_in_proof(step, mus_solver=MUS_SOLVER)
    assert decision is not None
    assert opposed is False
    assert decision.args[0] in (x, y)


def test_get_first_decision_partial_inputs():
    x, y = cp.intvar(1, 2, shape=2, name=("x", "y"))
    step = dict(
        input_lits=[x == 1],
        constraints=[cp.AllDifferent([x, y]), y == 1],
        output_lits=[cp.BoolVal(False)],
    )
    decision, opposed = get_first_decision_in_proof(step, mus_solver=MUS_SOLVER)
    assert decision is not None
    assert decision.args[0] is y


def test_get_first_decision_fully_assigned_inputs():
    x, y = cp.intvar(1, 2, shape=2, name=("x", "y"))
    step = dict(
        input_lits=[x == 1, y == 1],
        constraints=[cp.AllDifferent([x, y]), x == 1],
        output_lits=[cp.BoolVal(False)],
    )
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        decision, opposed = get_first_decision_in_proof(step, mus_solver=MUS_SOLVER)
    assert decision is None
    assert opposed is False
    assert any("No decisions" in str(w.message) for w in caught)


def test_get_nested_explanation_with_proof():
    model, _ = unsat_alldiff_model()
    path = tempfile.NamedTemporaryFile(suffix=".drcp", delete=False).name
    seq, orig = get_nested_explanation_with_proof(
        input_lits=[],
        constraints=list(model.constraints),
        output_lits=[cp.BoolVal(False)],
        proof_name=path,
        mus_solver=MUS_SOLVER,
        mus_algo="deletion",
        time_limit=60,
    )
    assert isinstance(seq, list)
    assert len(seq) > 0
    assert isinstance(orig, list)
    for step in seq:
        assert "input_lits" in step
        assert "constraints" in step
        assert "output_lits" in step
    assert any(isinstance(o, cp.expressions.core.BoolVal) and o.value() is False
               for o in seq[-1]["output_lits"])


def never_nest(step):
    return False


def test_find_explanation_sequence():
    model, _ = unsat_alldiff_model()
    path = tempfile.NamedTemporaryFile(suffix=".drcp", delete=False).name
    seq, proof = find_explanation_sequence(
        model,
        proof_name=path,
        mus_solver=MUS_SOLVER,
        mus_algo="deletion",
        time_limit=60,
        do_nested=never_nest,
    )
    assert len(seq) > 0
    assert len(proof) > 0
    assert not isinstance(proof[0], dict)
    assert any(isinstance(o, cp.expressions.core.BoolVal) and o.value() is False
               for o in seq[-1]["output_lits"])


def test_find_explanation_sequence_with_nesting():
    model, _ = unsat_alldiff_model()
    path = tempfile.NamedTemporaryFile(suffix=".drcp", delete=False).name
    seq, proof = find_explanation_sequence(
        model,
        proof_name=path,
        mus_solver=MUS_SOLVER,
        mus_algo="deletion",
        time_limit=60,
    )
    assert len(seq) > 0
    assert len(proof) > 0
    # nesting of the multi-constraint propagation step attaches a sub-sequence
    assert any("nested_explanation" in step for step in seq)
