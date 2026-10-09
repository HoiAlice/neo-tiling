"""Certified weak solvability at fixed prices (notes, chapter 4 examples)."""

from fractions import Fraction

from perturbation import Problem
from perturbation.datasets import berndt_wood, euklems, window
from perturbation.exact import weakly_solvable


def test_triangle_refuted():
    r = weakly_solvable(Problem.parse("4,1;3,3;1,4", "1,5,3"))
    assert r.solvable is False
    assert r.refutation == (1, -1, 1)  # y_2 <= y_1 + y_3
    assert all(any((S, t) in r.coverings for t in S) for S in [frozenset({1})])


def test_weakly_solvable_examples():
    for prices, outputs in [
        ("1,3;2,2;3,1;2,3", "1,1,1,2"),
        ("1,3;2,2;3,1;2,3", "2,1,1,1"),
        ("1,1;1,1", "1,1"),
    ]:
        r = weakly_solvable(Problem.parse(prices, outputs))
        assert r.solvable is True
        assert sum(r.masses.values()) > 0
        assert all(isinstance(m, Fraction) for m in r.masses.values())


def test_refutation_is_exact():
    """The refutation lambda is valid on every weakly reachable spectrum, exactly."""
    problem = window(euklems("UK", "C"), 0, 6)
    r = weakly_solvable(problem)
    assert r.solvable is False
    assert sum(lam * v for lam, v in zip(r.refutation, problem.y)) < 0
    assert all(sum(r.refutation[t] for t in S) >= 0 for S in r.reachable)


def test_real_windows_are_not_weakly_solvable():
    for problem in (window(berndt_wood(), 0, 6), window(euklems("US", "C"), 0, 6)):
        assert weakly_solvable(problem).solvable is False
