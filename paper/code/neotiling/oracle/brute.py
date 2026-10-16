"""Reference oracle for tiny instances (any d): enumeration of all weakly reachable sets."""

from __future__ import annotations

from ..geometry import reach
from . import OracleAnswer


_BRUTE_CACHE = {}


def oracle_brute(W, lo, hi):
    """Reference oracle for any d: all weakly reachable sets of W by exact enumeration, then an exact
    LP.  Returns an OracleAnswer with exact certificates (masses / Farkas vector).  Tiny |W| only."""
    key = tuple(W)
    if key not in _BRUTE_CACHE:
        if len(_BRUTE_CACHE) > 50:
            _BRUTE_CACHE.clear()
        _BRUTE_CACHE[key] = reach.all_reachable_sets([tuple(w) for w in W])
    cols = [S for S in _BRUTE_CACHE[key] if S]
    masses, lam = reach._cone_lp(cols, lo, hi)
    if masses is not None:
        keep = [(S, m) for S, m in zip(cols, masses) if m != 0]
        return OracleAnswer(True, [S for S, _ in keep], [m for _, m in keep])
    return OracleAnswer(False, lam=lam)
