"""Command line: python code/solve.py --P "4,1;3,3;1,4" --y "1,5,3" """

import argparse
from fractions import Fraction

from solvability import Prices, Solver


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Regular solvability of outputs y at prices P."
    )
    parser.add_argument("--P", required=True, help='prices, e.g. "4,1;3,3;1,4"')
    parser.add_argument("--y", required=True, help='outputs, e.g. "1,5,3"')
    parser.add_argument(
        "--no-h", action="store_true", help="only decide, do not construct h"
    )
    parser.add_argument(
        "--no-gp", action="store_true", help="do not bring h into general position"
    )
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    solver = Solver(
        Prices.parse(args.P),
        construct=not args.no_h,
        general_position=not args.no_gp,
        seed=args.seed,
    )
    print(solver.solve([Fraction(v.strip()) for v in args.y.split(",")]))


if __name__ == "__main__":
    main()
