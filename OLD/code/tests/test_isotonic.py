"""The dominance relaxation as a disjunctive isotonic regression (isotonic.py)."""

from perturbation import Problem, prepare
from perturbation.datasets import berndt_wood, select, window
from perturbation.isotonic import dominance_bb, isotonic

TOL = 1e-6


def test_isotonic_two_points():
    """q_0 <= q_1 with p = (2, 1): meeting at the geometric mean sqrt 2 costs
    2 (sqrt 2 - 1), less than moving one point alone (cost 1)."""
    value, q = isotonic([2.0, 1.0], [(0, 1)])
    assert abs(value - 2 * (2**0.5 - 1)) < TOL
    assert q[0] <= q[1] + TOL


def test_branch_and_bound_matches_relaxation_value():
    """BW capital and labour, 1947-56: rho_dom = rho = 0.6743228 (also the value of
    the cut loop)."""
    lower, best, _, finished = dominance_bb(
        prepare(window(select(berndt_wood(), (0, 1)), 0, 10))
    )
    assert finished
    assert abs(best - 0.6743228) < TOL
    assert abs(lower - best) < TOL


def test_cpp_matches_python():
    """The solver-free C++ branch and bound gives the same rho_dom."""
    from perturbation.cppdom import dominance_cpp  # noqa: PLC0415

    prep = prepare(window(select(berndt_wood(), (0, 1)), 0, 10))
    result = dominance_cpp(prep)
    assert result.finished
    assert abs(result.best - 0.6743228) < TOL
    assert len(result.a) == prep.T


def test_pure_cut_loop_gives_an_upper_bound():
    """Triangle: the pure restriction ends at certified weakly solvable prices; it
    cannot use the mixed witness of the optimum, so its value exceeds rho = 2/5."""
    from fractions import Fraction  # noqa: PLC0415

    from perturbation.cppdom import pure_cut_loop  # noqa: PLC0415

    problem = Problem.parse("4,1;3,3;1,4", "1,5,3")
    check, _, cuts = pure_cut_loop(problem, prepare(problem))
    assert cuts  # the pair (2, {1, 3}) has to be blocked
    assert check is not None
    assert check.certified
    assert check.total_pert >= Fraction(2, 5)


def test_no_conflicts_costs_nothing():
    _, best, nodes, finished = dominance_bb(prepare(Problem.parse("1,2;2,1", "1,1")))
    assert finished and best < TOL and nodes == 1
