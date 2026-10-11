"""Exact plane geometry and linear algebra over Q."""

from __future__ import annotations

from fractions import Fraction as F

Vec = tuple[F, F]


def hadamard(p: Vec, x: Vec) -> Vec:
    return (p[0] * x[0], p[1] * x[1])


def ip(a: Vec, x: Vec) -> F:
    return a[0] * x[0] + a[1] * x[1]


def det(u: Vec, v: Vec) -> F:
    return u[0] * v[1] - u[1] * v[0]


def line_through(a: Vec, b: Vec) -> Vec:
    """Normal xi with <xi, a> = <xi, b> = 1.

    Dually, the common point of the lines with normals a and b.
    """
    d = det(a, b)
    return ((b[1] - a[1]) / d, (a[0] - b[0]) / d)


def common_point(p: Vec, q: Vec) -> Vec | None:
    return None if det(p, q) == 0 else line_through(p, q)


def solve_linear(rows: list[list[F]], rhs: list[F]) -> list[F] | None:
    """One solution of rows * x = rhs (free variables set to 0), or None."""
    n = len(rows[0]) if rows else 0
    M = [[*row[:], b] for row, b in zip(rows, rhs)]
    pivots: list[int] = []
    for c in range(n):
        r = len(pivots)
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        M[r] = [v / M[r][c] for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                M[i] = [vi - M[i][c] * vr for vi, vr in zip(M[i], M[r])]
        pivots.append(c)
    if any(row[n] != 0 for row in M[len(pivots) :]):
        return None
    x = [F(0)] * n
    for i, c in enumerate(pivots):
        x[c] = M[i][n]
    return x
