"""Small examples from the notes (chapter "Критерий разрешимости"), solved with SCIP."""

from fractions import Fraction

import pytest

from perturbation import Problem, prepare, rational, solve, verify

TOL = 1e-5  # solver tolerance on the objective
DEN = 10  # the optima below are simple rationals, so a coarse conversion hits them


def run(prices: str, outputs: str, **kwargs):
    problem = Problem.parse(prices, outputs)
    solution = solve(prepare(problem), **kwargs)
    assert solution.status == "optimal"
    return problem, solution, verify(problem, rational(solution, DEN))


def test_unsolvable_triangle():
    """y = (1, 5, 3) at (4,1), (3,3), (1,4): index 2 covers {1, 3}. Moving p_2 to
    (5/2, 5/2) costs 2 (3 / (5/2) - 1) = 2/5, and nothing cheaper works."""
    _, solution, check = run("4,1;3,3;1,4", "1,5,3")
    assert abs(solution.value - 0.4) < TOL
    assert check.certified
    assert check.total_pert == Fraction(2, 5)


def test_solvable_no_general_position():
    _, solution, check = run("1,3;2,2;3,1;2,3", "2,1,1,1")
    assert abs(solution.value) < TOL
    assert check.certified and check.total_pert == 0


def test_weakly_solvable_but_not_solvable():
    """y = (1, 1, 1, 2) is not solvable (refutation y_4 <= y_1) but weakly solvable:
    {1,4} and {2,3,4} have weak witnesses, so rho = 0, the infimum not attained."""
    _, solution, check = run("1,3;2,2;3,1;2,3", "1,1,1,2")
    assert abs(solution.value) < TOL
    assert check.certified and check.total_pert == 0


def test_equal_prices_weakly_solvable():
    _, solution, check = run("1,1;1,1", "1,1")
    assert abs(solution.value) < TOL
    assert check.certified and check.total_pert == 0


def test_indicator_matches_big_m():
    _, bigm, _ = run("4,1;3,3;1,4", "1,5,3")
    _, ind, _ = run("4,1;3,3;1,4", "1,5,3", indicator=True)
    assert abs(bigm.value - ind.value) < TOL


def test_zero_outputs_are_fixed():
    """Only {2} is needed, and making it weakly reachable costs the same 2/5."""
    _, solution, check = run("4,1;3,3;1,4", "0,5,0")
    assert abs(solution.value - 0.4) < TOL
    assert check.certified and check.total_pert == Fraction(2, 5)
    assert {S for S, _ in solution.spectra} == {frozenset({1})}


@pytest.mark.parametrize("K", [1, 2])
def test_too_few_spectra_is_infeasible(K):
    """(1, 5, 3) takes three distinct positive values: two spectra cannot give it."""
    problem = Problem.parse("4,1;3,3;1,4", "1,5,3")
    assert solve(prepare(problem), K=K).status == "infeasible"


def test_three_spectra_suffice():
    _, full, _ = run("4,1;3,3;1,4", "1,5,3")
    _, three, _ = run("4,1;3,3;1,4", "1,5,3", K=3)
    assert abs(full.value - three.value) < TOL
