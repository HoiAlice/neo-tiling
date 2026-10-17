"""Logging of the solvers.  The modules log through `logging` (loggers `neotiling.*`); without `setup()` they are
silent.  INFO: the outer algorithm, every HiGHS call of the master (status, objective, bound, gap, nodes, time)
and any oracle subproblem slower than 2 s; DEBUG (verbose): every subproblem of the oracle and of the filters.

    logs.setup(verbose=False)
    with logs.run_file(logs.run_path(RESULTS, "lp_runs", "us3")):   # also write this run to a file
        solve(...)
"""

import logging
import os
import sys
import time

_t0 = time.time()


class _Formatter(logging.Formatter):
    def format(self, r):
        lvl = "" if r.levelno == logging.INFO else f"{r.levelname} "
        return (f"{time.strftime('%H:%M:%S', time.localtime(r.created))} {r.created - _t0:8.1f}s "
                f"{r.name.removeprefix('neotiling.'):15s} {lvl}{r.getMessage()}")


def setup(verbose=False):
    """Log to stderr, INFO or DEBUG."""
    root = logging.getLogger("neotiling")
    root.setLevel(logging.DEBUG if verbose else logging.INFO)
    if not root.handlers:
        h = logging.StreamHandler(sys.stderr)
        h.setFormatter(_Formatter())
        root.addHandler(h)
        root.propagate = False


class run_file:
    """Context manager: also write the records of the enclosed run to `path` (folders created)."""

    def __init__(self, path):
        self.path = os.path.abspath(path)

    def __enter__(self):
        os.makedirs(os.path.dirname(self.path), exist_ok=True)
        self.h = logging.FileHandler(self.path)
        self.h.setFormatter(_Formatter())
        logging.getLogger("neotiling").addHandler(self.h)
        return self.path

    def __exit__(self, *exc):
        logging.getLogger("neotiling").removeHandler(self.h)
        self.h.close()


def run_path(results, script, name):
    """<results>/logs/<script>/<YYYY-MM-DD>/<HHMMSS>_<name>.log"""
    safe = "".join(ch if ch.isalnum() or ch in "-_." else "_" for ch in name)
    return os.path.join(results, "logs", script, time.strftime("%Y-%m-%d"), f"{time.strftime('%H%M%S')}_{safe}.log")


def milp_summary(res, t):
    """One line about a finished scipy MILP/LP: status, objective, dual bound, gap, nodes, time."""
    parts = [str(res.message).split("(")[-1].rstrip(").") if "HiGHS Status" in str(res.message) else str(res.message)]
    if res.fun is not None:
        parts.append(f"obj {res.fun:.6g}")
    for k, fmt in (("mip_dual_bound", "bound {:.6g}"), ("mip_gap", "gap {:.2%}"), ("mip_node_count", "{} nodes"),
                   ("nit", "{} iterations")):
        v = getattr(res, k, None)
        if v is not None:
            parts.append(fmt.format(v))
    return ", ".join(parts) + f", {t:.2f}s"
