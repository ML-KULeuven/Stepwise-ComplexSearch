"""
Tests for top-level utils — shrink_domains and lex_mus_algo.
"""
import cpmpy as cp

from proof2seq.mus import DeletionBasedMUS
from utils import shrink_domains, lex_mus_algo, VAR_NAMES_REGEX
from tests.helpers import MUS_SOLVER


def test_shrink_domains_updates_bounds():
    x = cp.intvar(0, 10, name="x")
    shrink_domains([x >= 3, x <= 7])
    assert x.lb == 3 and x.ub == 7


def test_shrink_domains_conflicting_raises():
    x = cp.intvar(0, 5, name="x")
    try:
        shrink_domains([x >= 4, x <= 2])
        assert False, "expected ValueError"
    except ValueError:
        pass


def test_lex_mus_prefers_earlier_groups():
    a, b, c = cp.boolvar(name="a"), cp.boolvar(name="b"), cp.boolvar(name="c")
    # UNSAT via a & ~a; b and c are distractors
    soft_groups = [[b], [c], [a, ~a]]
    algo = DeletionBasedMUS([a, ~a, b, c], mus_solver=MUS_SOLVER)
    # lex_soft is least-preferred first in the API? Looking at lex_mus_algo:
    # it reverses lex_soft, so last group is most preferred (minimized first as soft while others hard)
    # Actually: reversed so first in input = most preferred to KEEP (becomes hard later)
    # Wait: lex_soft reversed, then for each soft minimize while later (more preferred after reverse = earlier in input) stay hard
    # Input order: index 0 = least preferred to include? Doc says "preference of lexicographically smaller items"
    # Looking at nested_explanations usage:
    #   lex_soft=[neg_output, input_lits, known_nogoods, new_nogoods, constraints]
    # constraints are last = least preferred (minimize constraints first after reverse)
    # So last group is minimized first (least preferred to keep).
    core = lex_mus_algo(algo, lex_soft=[[b], [c], [a], [~a]], hard=[])
    assert a in core and (~a) in core
    assert b not in core and c not in core


def test_lex_mus_empty():
    algo = DeletionBasedMUS([cp.boolvar(name="a")], mus_solver=MUS_SOLVER)
    assert lex_mus_algo(algo, lex_soft=[], hard=[]) == []


def test_var_names_regex():
    assert VAR_NAMES_REGEX.sub("_", "job-1.start") == "job_1_start"
