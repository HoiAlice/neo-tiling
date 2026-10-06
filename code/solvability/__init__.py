"""Regular solvability of outputs y at prices P.

See latex/notes.tex, section "Алгоритм регулярной разрешимости".

Prices -> ConeOracle -> Patching -> GeneralPositioner,  orchestrated by Solver.
"""

from .cone import ConeOracle, Decomposition, Obstruction
from .construction import Patching, PiecewiseLinear, Realization
from .general_position import GeneralPositioner
from .prices import Prices
from .solver import Construction, Decision, Solver

__all__ = [
    "ConeOracle",
    "Construction",
    "Decision",
    "Decomposition",
    "GeneralPositioner",
    "Obstruction",
    "Patching",
    "PiecewiseLinear",
    "Prices",
    "Realization",
    "Solver",
]
