"""The C++ solver of the dominance relaxation (code/cpp, `make` builds it).

`dominance_cpp` passes the normalized prices and the conflicting pairs to the binary
and returns its lower bound, best value and the best prices. The binary uses no
optimization solver: branch and bound over the coordinate of every conflicting pair
with exact isotonic regressions (minimum cuts) in the nodes. Its answer is certified
like any other point (`cuts.certify_point`); when y is weakly solvable there, the value
is rho itself.
"""

from __future__ import annotations

import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

import numpy as np

from .cuts import Cut, _integer_refutation, _killing_pairs, certify_point, separate
from .isotonic import conflicts

if TYPE_CHECKING:
    from .prep import Prepared, Problem

BINARY = Path(__file__).resolve().parent.parent / "cpp" / "build" / "dominance"


@dataclass(frozen=True)
class DominanceResult:
    lower: float  # lower bound on rho_dom (= best when finished)
    best: float  # value of the best feasible point of the relaxation
    nodes: int
    finished: bool
    a: tuple[tuple[float, ...], ...]  # multipliers q = p * a of the best point


def dominance_cpp(
    prep: Prepared, time_limit: float = 600.0, clauses: tuple = ()
) -> DominanceResult:
    """`clauses`: extra requirements "some pair (t, R) of the clause is blocked
    purely", i.e. q_t^i <= q_r^i for all r in R in one coordinate i (a restriction
    of blocking)."""
    if not BINARY.exists():
        subprocess.run(["make", "-C", str(BINARY.parent.parent)], check=True)
    pairs = conflicts(prep)
    lines = [f"{prep.T} {prep.d} {len(pairs)} {time_limit}"]
    lines += [" ".join(repr(x) for x in row) for row in prep.P]
    lines += [f"{t} {s}" for t, s in pairs]
    lines.append(str(len(clauses)))
    for clause in clauses:
        options = [(i, t, R) for t, R in clause for i in range(prep.d)]
        lines.append(str(len(options)))
        lines += [
            f"{i} {len(R)} " + " ".join(f"{t} {r}" for r in R) for i, t, R in options
        ]
    out = subprocess.run(
        [str(BINARY)],
        input="\n".join(lines),
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split("\n")
    lower, best, nodes, finished = out[0].split()
    rows = [list(map(float, line.split())) for line in out[1 : 1 + prep.T]]
    a = tuple(
        tuple(rows[t][i] / prep.P[t][i] for i in range(prep.d)) for t in range(prep.T)
    ) if len(rows) == prep.T and all(rows) else ()
    return DominanceResult(float(lower), float(best), int(nodes), finished == "1", a)


def pure_cut_loop(
    problem: Problem, prep: Prepared, time_limit: float = 600.0, max_iterations=200
):
    """Upper bounds without a nonconvex solver: the cut loop of `cuts.py` with every
    pair blocked only "purely" (one coordinate, linear), so each master is a
    disjunction of isotonic regressions solved by the C++ code. This master is a
    restriction, so its values are not lower bounds, but the loop ends at weakly
    solvable prices (finitely many cuts), which are certified exactly. Its cuts come
    from Farkas refutations and are valid for the exact problem too.
    Returns (certified answer or None, iterations, cuts)."""
    y = np.array(prep.y)
    clauses: list = []
    cuts: list[Cut] = []
    start = time.perf_counter()
    for iteration in range(1, max_iterations + 1):
        left = time_limit - (time.perf_counter() - start)
        if left <= 0:
            break
        result = dominance_cpp(prep, left, tuple(clauses))
        if not result.a:
            break
        Q = [
            [prep.P[t][i] * result.a[t][i] for i in range(prep.d)]
            for t in range(prep.T)
        ]
        answer = separate(Q, y)
        if answer[0] == "yes":
            return certify_point(problem, prep, result.a), iteration, tuple(cuts)
        w = _integer_refutation(answer[1], problem.y)
        pairs = _killing_pairs(Q, w, answer[2])
        if pairs in clauses:
            break
        clauses.append(pairs)
        cuts.append(Cut(pairs, w))
    return None, iteration, tuple(cuts)
