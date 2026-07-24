"""
Tests for proof2seq.mus — soft/hard MUS with dynamic assumption maps.
"""
import cpmpy as cp

from proof2seq.mus import DeletionBasedMUS, SMUS, QuickXplain, Marco
from tests.helpers import MUS_SOLVER


def _conflicting_bools():
    a, b = cp.boolvar(name="a"), cp.boolvar(name="b")
    return a, b, [a, ~a, b]


def test_deletion_mus_core():
    a, b, cons = _conflicting_bools()
    algo = DeletionBasedMUS(cons, mus_solver=MUS_SOLVER)
    core = algo.get_mus(soft=cons, hard=[])
    assert a in core and (~a) in core
    assert b not in core


def test_quickxplain_core():
    a, b, cons = _conflicting_bools()
    algo = QuickXplain(cons, mus_solver=MUS_SOLVER)
    core = algo.get_mus(soft=cons, hard=[])
    assert a in core and (~a) in core
    assert b not in core


def test_smus_core():
    a, b, cons = _conflicting_bools()
    algo = SMUS(cons, mus_solver=MUS_SOLVER, hs_solver=MUS_SOLVER)
    core = algo.get_mus(soft=cons, hard=[])
    assert a in core and (~a) in core
    assert b not in core
    assert len(core) == 2


def test_marco_yields_mus():
    a, b, cons = _conflicting_bools()
    algo = Marco(cons, mus_solver=MUS_SOLVER, map_solver="pysat")
    core = next(algo.get_mus(soft=cons, hard=[], max_musses=1))
    assert a in core and (~a) in core
    assert b not in core


def test_get_assumps_registers_new_soft():
    a, b, cons = _conflicting_bools()
    algo = DeletionBasedMUS(cons, mus_solver=MUS_SOLVER)

    n_before = len(algo.assump)
    extra = a | b
    soft_assumps = algo.get_assumps([extra])
    assert len(algo.assump) == n_before + 1
    assert extra in algo.rev_map
    assert algo.dmap[soft_assumps[0]] is extra
    assert extra in algo.cons


def test_get_assumps_registers_new_hard():
    a, b, cons = _conflicting_bools()
    algo = DeletionBasedMUS(cons, mus_solver=MUS_SOLVER)

    n_before = len(algo.assump)
    hard_extra = ~b
    hard_assumps = algo.get_assumps([hard_extra])
    assert len(algo.assump) == n_before + 1
    assert hard_extra in algo.rev_map
    assert algo.dmap[hard_assumps[0]] is hard_extra


def test_get_assumps_reuses_existing():
    a, b, cons = _conflicting_bools()
    algo = DeletionBasedMUS(cons, mus_solver=MUS_SOLVER)
    first = algo.get_assumps([a])
    second = algo.get_assumps([a])
    assert first == second
    assert len(algo.assump) == len(cons)


def test_get_assumps_skips_true():
    a, b, cons = _conflicting_bools()
    algo = DeletionBasedMUS(cons, mus_solver=MUS_SOLVER)
    assumps = algo.get_assumps([cp.BoolVal(True), a])
    assert len(assumps) == 1
    assert algo.dmap[assumps[0]] is a


def test_mus_with_hard_constraint():
    a, b = cp.boolvar(name="a"), cp.boolvar(name="b")
    # soft: a, b, ~b ; hard: ~a  → core should involve b and ~b (a is not needed once ~a is hard)
    soft = [a, b, ~b]
    hard = [~a]
    algo = DeletionBasedMUS(soft + hard, mus_solver=MUS_SOLVER)
    core = algo.get_mus(soft=soft, hard=hard)
    assert b in core and (~b) in core
    assert a not in core


def test_empty_soft_returns_empty():
    a, b, cons = _conflicting_bools()
    algo = SMUS(cons, mus_solver=MUS_SOLVER, hs_solver=MUS_SOLVER)
    assert algo.get_mus(soft=[], hard=[a, ~a]) == []
