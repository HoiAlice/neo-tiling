"""Minimal perturbation for the six planar Berndt-Wood series and three costs.

Usage: ../.venv/bin/python run_bw.py [cost ...]   (costs: log pi eps; default all)
Writes results/bw_<cost>.txt.
"""

import sys
import time
from pathlib import Path

import data
import perturb2d as pt
import planar

OUT = Path(__file__).resolve().parent / "results"


def main(costs):
    OUT.mkdir(exist_ok=True)
    for name in costs:
        cost = pt.COSTS[name]
        lines = [f"cost {cost.name}", "pair  T  lower  upper  gap  iterations  cuts  nodes  "
                 "seconds  certified"]
        for pair in data.PAIRS:
            P, y, _ = data.berndt_wood(pair)
            t0 = time.time()
            r = pt.solve(P, y, cost, time_limit=1800)
            ok = planar.check_certificate(r.Q, y, r.certificate)
            line = (f"{pair}  {len(P)}  {r.lower:.7f}  {r.upper:.7f}  "
                    f"{r.upper - r.lower:.1e}  {r.iterations}  {r.cuts}  {r.nodes}  "
                    f"{time.time() - t0:.1f}  {ok}")
            print(name, line, flush=True)
            lines.append(line)
        (OUT / f"bw_{name}.txt").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main(sys.argv[1:] or ["log", "pi", "eps"])
