"""Real-data instances: `pytest -m slow`. Small windows are solved exactly and must be
certified; longer windows run in the heuristic mode and only have to produce a feasible,
exactly verified answer within the hyperbola bound."""

import pytest

from perturbation import prepare, rational, solve, verify
from perturbation.datasets import berndt_wood, euklems, window

TOL = 1e-4
DEN = 10**6
EXACT_UP_TO = 4  # measured: T = 6, d = 4 does not close its gap in 300 s


def check(problem, time_limit):
    prep = prepare(problem)
    exact = problem.T <= EXACT_UP_TO
    solution = solve(prep, time_limit=time_limit, exact=exact)
    print(
        f"T={problem.T} d={problem.d} D={prep.D:.4g} {solution.status} "
        f"value={solution.value:.6g} bound={solution.bound:.6g} {solution.seconds:.1f}s"
    )
    assert solution.spectra, "no feasible point found"
    assert solution.value <= prep.D + TOL  # the hyperbola point is feasible
    if exact:
        assert solution.status == "optimal"
    report = verify(problem, rational(solution, DEN))
    assert report.mass_error == 0
    return solution


@pytest.mark.slow
@pytest.mark.parametrize("n", [4, 6, 8])
def test_berndt_wood_windows(n):
    check(window(berndt_wood(), 0, n), time_limit=600)


@pytest.mark.slow
@pytest.mark.parametrize("geo", ["UK", "US"])
@pytest.mark.parametrize("n", [4, 6])
def test_euklems_windows(geo, n):
    check(window(euklems(geo, "C"), 0, n), time_limit=600)


@pytest.mark.slow
def test_berndt_wood_full():
    check(berndt_wood(), time_limit=1800)


@pytest.mark.slow
def test_euklems_uk_full():
    check(euklems("UK", "C"), time_limit=1800)
