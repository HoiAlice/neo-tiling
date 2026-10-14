"""Nested partitions of the witness simplex.

A weak witness of index t is a point xi of the simplex {xi >= 0, sum xi = 1}. The
masters never use xi itself, only a partition of the simplex into cells:

* lower master: xi lies in some cell, so for every s the inequality <xi, q_s - q_t> >= 0
  holds at some vertex of that cell (a linear function on a simplex attains its
  maximum at a vertex). This is a relaxation;
* upper master: xi is a vertex of the partition. This is a restriction.

Cells are simplices with exact rational vertices, refined by longest-edge bisection,
so the diameter of every cell that is bisected often enough tends to zero.
"""

from __future__ import annotations

from fractions import Fraction

Vertex = tuple[Fraction, ...]


class SimplexGrid:
    """A partition of the standard simplex in R^d into simplicial cells."""

    def __init__(self, d: int):
        self.d = d
        unit = [tuple(Fraction(int(i == j)) for j in range(d)) for i in range(d)]
        self.vertices: list[Vertex] = []
        self._index: dict[Vertex, int] = {}
        self.cells: list[tuple[int, ...]] = [tuple(self._vertex(v) for v in unit)]

    def _vertex(self, v: Vertex) -> int:
        if v not in self._index:
            self._index[v] = len(self.vertices)
            self.vertices.append(v)
        return self._index[v]

    @staticmethod
    def _dist2(a: Vertex, b: Vertex) -> Fraction:
        return sum((x - y) ** 2 for x, y in zip(a, b))

    def diameter2(self, cell: int) -> Fraction:
        vs = [self.vertices[i] for i in self.cells[cell]]
        return max(
            (self._dist2(a, b) for i, a in enumerate(vs) for b in vs[i + 1 :]),
            default=Fraction(0),
        )

    def bisect(self, cell: int) -> None:
        """Split the cell at the midpoint of its longest edge (ties: first edge)."""
        ids = self.cells[cell]
        best, pair = Fraction(-1), (0, 1)
        for a in range(len(ids)):
            for b in range(a + 1, len(ids)):
                dd = self._dist2(self.vertices[ids[a]], self.vertices[ids[b]])
                if dd > best:
                    best, pair = dd, (a, b)
        a, b = pair
        va, vb = self.vertices[ids[a]], self.vertices[ids[b]]
        mid = self._vertex(tuple((x + y) / 2 for x, y in zip(va, vb)))
        left = tuple(mid if i == a else v for i, v in enumerate(ids))
        right = tuple(mid if i == b else v for i, v in enumerate(ids))
        self.cells[cell] = left
        self.cells.append(right)

    def refine_coarsest(self) -> None:
        """Bisect every cell of maximal diameter (makes the mesh go to zero)."""
        top = max(self.diameter2(c) for c in range(len(self.cells)))
        for c in [c for c in range(len(self.cells)) if self.diameter2(c) == top]:
            self.bisect(c)

    def contains(self, cell: int, xi: Vertex) -> bool:
        """Exact test: xi lies in the cell (nonnegative barycentric coordinates)."""
        from sympy import Matrix

        A = Matrix([[*self.vertices[i]] for i in self.cells[cell]]).T
        lam, params = A.gauss_jordan_solve(Matrix(xi))
        lam = lam.subs({p: 0 for p in params})
        return all(x >= 0 for x in lam)

    def bisect_towards(self, cell: int, xi: Vertex, depth: int) -> None:
        """Bisect the cell, then `depth - 1` more times the child that contains xi."""
        for _ in range(depth):
            self.bisect(cell)
            if not self.contains(cell, xi):
                cell = len(self.cells) - 1

    def subdivide(self, cell: int, depth: int) -> None:
        """Bisect the cell and all its descendants `depth` times (2^depth pieces)."""
        group = [cell]
        for _ in range(depth):
            nxt = []
            for c in group:
                self.bisect(c)
                nxt += [c, len(self.cells) - 1]
            group = nxt

    def used_vertices(self) -> list[int]:
        return sorted({i for ids in self.cells for i in ids})
