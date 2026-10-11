"""Minimal perturbation for the planar slices of EU KLEMS: 5 countries x 8 industries x 3
pairs of inputs (K = capital, L = labour, I = intermediates).

Usage: ../.venv/bin/python run_klems.py cost [time_limit] [geo ...]   (cost: log pi eps)
Writes results/klems_<cost>_<geos>.txt.
"""

import sys
import time
from pathlib import Path

import data
import perturb2d as pt
import planar

OUT = Path(__file__).resolve().parent / "results"


def main(name, limit, geos):
    OUT.mkdir(exist_ok=True)
    cost = pt.COSTS[name]
    lines = [f"cost {cost.name}, time limit {limit:.0f} s",
             "series  T  lower  upper  gap  iterations  cuts  pair_cuts  nodes  seconds  "
             "certified"]
    out = OUT / f"klems_{name}_{'-'.join(geos)}.txt"
    for geo in geos:
        for ind in data.INDUSTRIES:
            for pair in data.KLEMS_PAIRS:
                P, y, _ = data.euklems(geo, ind, pair)
                t0 = time.time()
                r = pt.solve(P, y, cost, time_limit=limit)
                ok = planar.check_certificate(r.Q, y, r.certificate)
                npair = r.cuts - sum(1 for t in range(len(y)) for s in range(len(y))
                                     if y[t] > y[s])
                tag = f"{geo}:{ind}:{''.join(data.KLEMS_NAMES[i] for i in pair)}"
                line = (f"{tag}  {len(P)}  {r.lower:.7f}  {r.upper:.7f}  "
                        f"{r.upper - r.lower:.1e}  {r.iterations}  {r.cuts}  {npair}  "
                        f"{r.nodes}  {time.time() - t0:.1f}  {ok}")
                print(line, flush=True)
                lines.append(line)
                out.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main(sys.argv[1], float(sys.argv[2]) if len(sys.argv) > 2 else 600.0,
         sys.argv[3:] or list(data.GEOS))
