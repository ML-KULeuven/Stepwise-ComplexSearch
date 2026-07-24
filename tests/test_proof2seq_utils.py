"""
Tests for proof2seq.utils — normalize, domains, sanity checks, stats.
"""
import cpmpy as cp
from cpmpy.expressions.core import BoolVal

from proof2seq.utils import (
    normalize, get_variables, get_domains_from_literals, literals_from_domains,
    minimize_literals, sanity_check_nogoods,
    get_proof_statistics, sanity_check_sequence,
)


def test_normalize_comparisons():
    x = cp.intvar(0, 5, name="x")
    out = normalize([x < 3, x > 1])
    assert (x <= 2) in out
    assert (x >= 2) in out


def test_normalize_boolvars():
    b = cp.boolvar(name="b")
    out = normalize([b, ~b])
    assert (b >= 1) in out
    assert (b <= 0) in out


def test_get_variables_nested():
    x, y = cp.intvar(0, 1, shape=2, name=("x", "y"))
    vs = get_variables([[x == 1], (y != 0,)])
    assert set(vs) == {x, y}


def test_domains_from_literals_and_back():
    x = cp.intvar(0, 5, name="x")
    domains = get_domains_from_literals([x >= 2, x <= 4])
    assert domains[x] == {2, 3, 4}
    mini = minimize_literals([x >= 2, x <= 4, x != 5])
    assert len(mini) >= 1
    # bounds should still describe {2,3,4}
    dom2 = get_domains_from_literals(mini)
    assert dom2[x] == {2, 3, 4}


def test_minimize_literals_false():
    assert minimize_literals([cp.BoolVal(False), cp.boolvar(name="a")]) == [cp.BoolVal(False)]


def test_sanity_check_nogoods_ok():
    a = cp.boolvar(name="a")
    sanity_check_nogoods([a, ~a, cp.BoolVal(False)], constraints=[])


def test_sanity_check_nogoods_rejects_non_expr():
    try:
        sanity_check_nogoods([1, 2])
        assert False, "expected ValueError"
    except ValueError:
        pass


def test_get_proof_statistics_expressions():
    x = cp.intvar(0, 2, name="x")
    stats = get_proof_statistics([x == 1, (x != 1) | (x == 0), cp.BoolVal(False)])
    assert stats["length"] == 3
    assert "avg_vars" in stats


def test_get_proof_statistics_empty():
    stats = get_proof_statistics([])
    assert stats["length"] == 0


def test_sanity_check_sequence():
    x = cp.intvar(0, 2, name="x")
    seq = [
        dict(input_lits=[], constraints=[x != 1], output_lits=[x != 1]),
        dict(input_lits=[x != 1], constraints=[x != 0, x != 2], output_lits=[cp.BoolVal(False)]),
    ]
    # second step: x!=1, x!=0, x!=2 implies False over domain {0,1,2}
    sanity_check_sequence(seq)
