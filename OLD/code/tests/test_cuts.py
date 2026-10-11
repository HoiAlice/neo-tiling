"""The covering-cut algorithm (perturbation/cuts.py): proved lower bound plus an exactly
verified answer, on the examples of the notes and on short real-data windows."""

from fractions import Fraction

import pytest

from perturbation import Problem, prepare
from perturbation.cuts import certify, solve_cuts
from perturbation.datasets import berndt_wood, select, window
from perturbation.primal import repair, strict_point, upper_bound

TOL = 1e-6  # solver tolerances on the values


def run(problem: Problem):
    prep = prepare(problem)
    solution = solve_cuts(prep, upper=lambda a: upper_bound(problem, prep, a))
    assert solution.status == "optimal"
    check = certify(problem, prep, solution)
    assert check is not None
    assert check.certified
    # the certified answer is an upper bound, the master value a lower bound
    assert solution.bound <= float(check.total_pert) + TOL
    assert float(check.total_pert) <= solution.bound + TOL
    return solution, check


def test_triangle_needs_a_pair_cut():
    """y = (1, 5, 3) at (4,1), (3,3), (1,4): no dominance, but 2 covers {1, 3}; one cut
    with the pair (2, {1, 3}) gives rho = 2/5."""
    solution, _ = run(Problem.parse("4,1;3,3;1,4", "1,5,3"))
    assert abs(solution.bound - 0.4) < TOL
    assert any(len(R) == 2 for cut in solution.cuts for _, R in cut.pairs)  # noqa: PLR2004


def test_weakly_solvable_at_p():
    solution, check = run(Problem.parse("1,3;2,2;3,1;2,3", "1,1,1,2"))
    assert abs(solution.bound) < TOL
    assert check.total_pert < Fraction(1, 10**6)


@pytest.mark.parametrize(
    ("n", "rho"),
    [(4, 0.0676458), (6, 0.3150733), (10, 0.6743228)],
)
def test_berndt_wood_capital_labour(n, rho):
    """d = 2: the dominance cuts alone give the optimum on these windows."""
    solution, _ = run(window(select(berndt_wood(), (0, 1)), 0, n))
    assert all(len(cut.pairs) == 1 for cut in solution.cuts)
    assert abs(solution.bound - rho) < 1e-6  # noqa: PLR2004


def test_berndt_wood_four_inputs():
    solution, _ = run(window(berndt_wood(), 0, 6))
    assert abs(solution.bound - 0.1465855) < 1e-6  # noqa: PLR2004


@pytest.mark.slow
@pytest.mark.parametrize(
    ("name", "rho"),
    [("bw", 1.5109552), ("UK:C", 0.8049211), ("JP:TOT", 0.3071898)],
)
def test_full_series(name, rho):
    """Whole series, T = 22-25, d = 3, 4: certified in seconds."""
    from perturbation.datasets import euklems  # noqa: PLC0415

    problem = berndt_wood() if name == "bw" else euklems(*name.split(":"))
    solution, _ = run(problem)
    assert abs(solution.bound - rho) < 1e-5  # noqa: PLR2004


def test_matches_branch_and_bound():
    """A small random-like instance where the old exact model is fast."""
    from perturbation import solve  # noqa: PLC0415

    problem = Problem.parse("58,72;100,60;58,66;76,25", "4,2,1,8")
    exact = solve(prepare(problem), exact=True)
    solution, _ = run(problem)
    assert exact.status == "optimal"
    assert abs(solution.bound - exact.value) < 1e-5  # noqa: PLR2004


def test_repair_gives_an_upper_bound():
    """The repair of P itself (y not weakly solvable there) is weakly solvable and
    costs at least rho = 2/5."""
    problem = Problem.parse("4,1;3,3;1,4", "1,5,3")
    prep = prepare(problem)
    a = repair(prep, [[1.0, 1.0]] * 3)
    assert a is not None
    check = upper_bound(problem, prep, a)
    assert check is not None
    assert check.certified
    assert check.total_pert >= Fraction(2, 5) - Fraction(1, 10**6)


def test_strict_point_is_solvable_and_close():
    """The tilt of the certified weak answer is strictly solvable and costs a bit
    more than rho = 2/5."""
    problem = Problem.parse("4,1;3,3;1,4", "1,5,3")
    _, check = run(problem)
    strict = strict_point(problem, check)
    assert strict is not None
    _, total, _ = strict
    assert Fraction(2, 5) < total < Fraction(2, 5) + Fraction(1, 10**4)
