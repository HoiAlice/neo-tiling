"""Box oracles and their common interface.

An oracle decides, for points W (here: the 2T corners L_1..L_T, U_1..U_T) and bounds lo <= hi,

    exists w in cone{1_S : S weakly reachable at W} with lo <= w <= hi      (componentwise)

and is called as `oracle(W, lo, hi)`.  It returns either a bool or an `OracleAnswer`; use `as_answer`
to normalise.  Implementations: `oracle.brute.oracle_brute` (any d, tiny W, exact),
`oracle.flow_d2.oracle_flow` (d = 2, polynomial), `oracle.exact.oracle_exact` (any d, exact geometry).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional


@dataclass
class OracleAnswer:
    """Answer of a box oracle.  feasible: the decision.  Optional certificates (None = not supplied):
    YES: `columns` (list of frozensets of point indices, each weakly reachable at W) and `masses`
    (Fractions >= 0) with lo <= sum m_S 1_S <= hi.
    NO: `lam` (Farkas vector over the points, see `reach.check_farkas`) and, for `oracle_exact`,
    `covers`: the cover cuts C = [(t, A)] used by the NO proof, i.e. lam(S) >= 0 for every S that
    satisfies x_t <= sum_{s in A} x_s for all (t, A) in C (the NO holds at every box where the covers
    of C are present)."""
    feasible: bool
    columns: Optional[list] = None
    masses: Optional[list] = None
    lam: Optional[list] = None
    covers: Optional[list] = None


BoxOracle = Callable[[list, list, list], "bool | OracleAnswer"]


def as_answer(res):
    return res if isinstance(res, OracleAnswer) else OracleAnswer(bool(res))


class CountingOracle:
    """Wraps an oracle and counts calls."""

    def __init__(self, oracle):
        self.oracle = oracle
        self.count = 0

    def __call__(self, W, lo, hi):
        self.count += 1
        return self.oracle(W, lo, hi)
