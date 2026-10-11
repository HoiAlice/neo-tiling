"""Command line.

python code/solve.py --P "4,1;3,3;1,4" --y "1,5,3"         decide y, build h for it
python code/solve.py --P "4,1;3,3;1,4" --spectra "1;2,3"   h for given spectra
python code/solve.py --P "4,1;3,3;1,4" --all               h with Sp(h, P) = Sp(P)
"""

import argparse
import sys
from fractions import Fraction

from solvability import Prices, Solver


def parse_spectra(text: str) -> list[frozenset[int]]:
    """'1;2,3' -> [{0}, {1, 2}] (indices are 1-based on the command line)."""
    return [
        frozenset(int(t) - 1 for t in part.split(",") if t.strip())
        for part in text.split(";")
    ]


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--P", required=True, help='prices, e.g. "4,1;3,3;1,4"')
    task = parser.add_mutually_exclusive_group(required=True)
    task.add_argument("--y", help='outputs to decide, e.g. "1,5,3"')
    task.add_argument("--spectra", help='spectra for h, e.g. "1;2,3" (1-based)')
    task.add_argument("--all", action="store_true", help="h for all reachable spectra")
    parser.add_argument("--no-h", action="store_true", help="do not build h")
    parser.add_argument("--no-gp", action="store_true", help="skip general position (always skipped if P is not)")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    prices = Prices.parse(args.P)
    solver = Solver(prices, general_position=not args.no_gp, seed=args.seed)
    masses = None
    if args.y is not None:
        decision = solver.decide([Fraction(v.strip()) for v in args.y.split(",")])
        print(decision)
        if not decision.solvable:
            return
        masses = decision.verdict.masses
        spectra = list(masses)
    elif args.all:
        spectra = prices.reachable_spectra
    else:
        spectra = parse_spectra(args.spectra)
    if args.no_h:
        return
    try:
        print(solver.construct(spectra, masses))
    except ValueError as error:
        sys.exit(str(error))


if __name__ == "__main__":
    main()
