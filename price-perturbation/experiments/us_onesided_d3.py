"""One-sided profile on the US data at d = 3 (K, L, II normalised by the output price GO), weights
zono.default_weights, exact oracle exact_oracle.oracle_exact.  Prints the profile, the spread of
ln(p_i/p_GO) before and after, the singular values of the centred cloud ln Q (line / plane), and the
exact check of the rational solution (onesided.rational_solution).
Run: nice -n 19 ../.venv/bin/python experiments/us_onesided_d3.py
"""

import time

import numpy as np

import _common  # noqa: F401
from perturb import onesided, zono
from perturb.data import load_us_d3
from perturb.exact_oracle import oracle_exact

NAMES3 = ["K", "L", "II", "GO"]


def main():
    P, y, years = load_us_d3()
    P = [tuple(float(c) for c in p) for p in P]
    T = len(P)
    kap, k0 = zono.default_weights(years, 3, NAMES3)
    t0 = time.time()
    out = onesided.profile(P, y, kap, k0, oracle_exact, tol=1e-6,
                           log=lambda s: print(f"  [{time.time() - t0:.0f}s] {s}", flush=True))
    print(f"d = 3: rho* {out['stages'][0]['lam']:.5f}, {len(out['stages'])} stages, {out['calls']} calls, "
          f"{time.time() - t0:.1f}s, ties {out['ties']}, verified {out['verified']}, tight {out['tight']}, "
          f"both {out['both']}")
    for i, n in enumerate(NAMES3[:3]):
        print(f"std ln({n}/GO): {np.std(np.log([p[i] for p in P])):.4f} -> "
              f"{np.std(np.log([q[i] for q in out['Q']])):.4f}")
    for name, X in (("P", P), ("Q", out["Q"])):           # shape of the cloud ln X: line / plane
        L = np.log(np.array(X, dtype=float))
        print(f"singular values of centred ln {name}: "
              + ", ".join(f"{s:.4f}" for s in np.linalg.svd(L - L.mean(0), compute_uv=False)))
    Qr, ans = onesided.rational_solution(P, y, kap, k0, out, oracle_exact)
    print(f"rational Q (corners rounded inwards): weakly solvable exactly: {ans.feasible}, "
          f"{len(ans.columns or [])} sets in the certificate")
    print("year  theta_t")
    for t in range(T):
        print(f"{years[t]}  {out['theta'][t]:+.6f}")


if __name__ == "__main__":
    main()
