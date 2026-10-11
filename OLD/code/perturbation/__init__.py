"""Minimal perturbation of prices (notes, chapter "Минимальное возмущение цен").

Given prices P (T vectors in R^d_{++}) and outputs y >= 0, find prices Q at which y is
weakly solvable and the total perturbation pi(P, Q) = sum_{t,i} max(|q/p-1|, |p/q-1|) is
minimal. By the notes this minimum equals rho(P, y), the infimum over solvable prices.

prep.py    normalization, the bound D(kappa), the hyperbola start point
model.py   the mixed-integer bilinear model (def:model) for SCIP via PySCIPOpt
verify.py  exact rational verification of a solution (weak witnesses and masses)
"""

from .model import Solution, solve
from .prep import Prepared, Problem, prepare
from .verify import Rational, Verification, rational, verify

__all__ = [
    "Prepared",
    "Problem",
    "Rational",
    "Solution",
    "Verification",
    "prepare",
    "rational",
    "solve",
    "verify",
]
