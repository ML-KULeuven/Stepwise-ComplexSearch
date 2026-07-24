"""
Tests for proof2seq.pipeline — parse → filter → minimize pipeline.
"""
import tempfile

import cpmpy as cp

from proof2seq.pipeline import (
    compute_explanation_proof, finalize_sequence, syntactic_minimize_literals,
    keep_user_var_nogoods, is_domain_reduction,
)
from proof2seq.utils import get_variables, sanity_check_nogoods
from tests.helpers import unsat_alldiff_model, MUS_SOLVER


def test_keep_user_var_nogoods():
    x, y = cp.intvar(0, 1, shape=2, name=("x", "y"))
    aux = cp.boolvar(name="aux")
    keep = keep_user_var_nogoods([x, y])
    assert keep(x == 1) is True
    assert keep(aux >= 1) is False
    assert keep(cp.BoolVal(False)) is True


def test_is_domain_reduction_helper():
    x, y = cp.intvar(0, 1, shape=2, name=("x", "y"))
    assert is_domain_reduction(x == 1) is True
    assert is_domain_reduction((x != 1) | (y != 1)) is False
    assert is_domain_reduction(cp.BoolVal(False)) is True


def test_compute_explanation_proof_phases_noop():
    model, _ = unsat_alldiff_model()
    path = tempfile.NamedTemporaryFile(suffix=".drcp", delete=False).name
    proof, orig = compute_explanation_proof(
        model,
        minimize_phase1=False,
        minimize_phase2=False,
        mus_solver=MUS_SOLVER,
        mus_type="mus",
        proof_name=path,
        do_sanity_check=True,
    )
    assert isinstance(proof, list)
    assert isinstance(orig, list)
    assert len(orig) >= len(proof)  # domain-reduction filter may drop some
    for ng in proof:
        assert is_domain_reduction(ng)
    sanity_check_nogoods(proof, model.constraints)


def test_compute_explanation_proof_with_minimize():
    model, _ = unsat_alldiff_model()
    path = tempfile.NamedTemporaryFile(suffix=".drcp", delete=False).name
    proof, orig = compute_explanation_proof(
        model,
        minimize_phase1=True,
        minimize_phase2=True,
        mus_solver=MUS_SOLVER,
        mus_type="mus",
        proof_name=path,
    )
    assert 0 < len(proof) <= len(orig)
    sanity_check_nogoods(proof, model.constraints)


def test_syntactic_minimize_literals():
    x = cp.intvar(0, 10, name="x")
    lits = [x <= 5, x <= 3, x >= 1, x >= 0]
    out = syntactic_minimize_literals(lits)
    assert (x <= 3) in out
    assert (x >= 1) in out
    assert (x <= 5) not in out


def test_finalize_sequence_merges_equal_constraints():
    x = cp.intvar(0, 5, name="x")
    seq = [
        dict(input_lits=[], constraints=[x >= 0], output_lits=[x <= 4]),
        dict(input_lits=[x <= 4], constraints=[x >= 0], output_lits=[x <= 2]),
        dict(input_lits=[x <= 2], constraints=[x == 1], output_lits=[cp.BoolVal(False)]),
    ]
    out = finalize_sequence(seq)
    assert len(out) == 2  # first two merge (same constraints)
    assert set(out[0]['constraints']) == {x >= 0}
    assert cp.BoolVal(False) in out[1]['output_lits']
