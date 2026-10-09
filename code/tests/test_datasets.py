"""Loaders of the real-data instances (fast)."""

import pytest

from perturbation import prepare
from perturbation.datasets import berndt_wood, euklems, window

T_BW, D_BW = 25, 4
T_EU, D_EU = 26, 3
T_UK = 22  # the UK file has no previous-year prices before 1999


def test_berndt_wood_shape():
    problem = berndt_wood()
    assert (problem.T, problem.d) == (T_BW, D_BW)
    assert problem.P[0] == (1, 1, 1, 1)  # 1947 is the base year of the price indices
    assert all(v > 0 for v in problem.y)


@pytest.mark.parametrize("geo", ["UK", "US", "DE", "FR", "JP"])
def test_euklems_manufacturing(geo):
    problem = euklems(geo, "C")
    assert (problem.T, problem.d) == (T_UK if geo == "UK" else T_EU, D_EU)
    assert all(c > 0 for p in problem.P for c in p)
    assert all(v > 0 for v in problem.y)


def test_uk_volumes_are_chain_linked():
    """The UK file has no price indices; chained volumes must still be smooth."""
    problem = euklems("UK", "C")
    ratios = [float(b / a) for a, b in zip(problem.y, problem.y[1:])]
    assert all(0.8 < r < 1.25 for r in ratios)  # noqa: PLR2004


def test_window_and_prepare():
    problem = window(berndt_wood(), 0, 6)
    prep = prepare(problem)
    assert problem.T == 6  # noqa: PLR2004
    assert prep.D >= 0
    assert all(max(p) == 1 for p in zip(*prep.P))  # normalized per coordinate
