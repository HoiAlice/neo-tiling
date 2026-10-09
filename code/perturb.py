"""Command line for the minimal perturbation problem.

python code/perturb.py --P "4,1;3,3;1,4" --y "1,5,3"
python code/perturb.py --data bw --time 1800
python code/perturb.py --data euklems:UK:C --window 1999:8 --exact

First the certified test of weak solvability at P (rho = 0?), then the solver: the
heuristic mode by default (aggressive heuristics, stop on stall, no start point, no
certificate), or `--exact` for the full branch and bound; then the exact rational check
of the answer and the report of the price changes.
"""

import argparse

from perturbation import Problem, prepare, rational, solve, verify
from perturbation.datasets import berndt_wood, euklems, select, window
from perturbation.exact import MAX_T, weakly_solvable
from perturbation.report import describe


def load(args) -> Problem:
    if args.data is None:
        return Problem.parse(args.P, args.y)
    if args.data == "bw":
        problem = berndt_wood()
    elif args.data.startswith("euklems:"):
        _, geo, industry = args.data.split(":")
        problem = euklems(geo, industry)
    else:
        raise SystemExit(f"unknown dataset {args.data}")
    if args.inputs:
        names = args.inputs.split(",")
        problem = select(problem, tuple(problem.factors.index(n) for n in names))
    if args.window:
        first, n = args.window.split(":")
        start = problem.periods.index(first) if problem.periods else int(first)
        problem = window(problem, start, int(n))
    return problem


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--P", help='prices, rows by ";", e.g. "4,1;3,3;1,4"')
    parser.add_argument("--y", help='outputs, e.g. "1,5,3"')
    parser.add_argument("--data", help="bw | euklems:GEO:INDUSTRY")
    parser.add_argument(
        "--inputs", help="keep only these inputs, e.g. capital,labour (d = 2)"
    )
    parser.add_argument("--window", help="FIRST:N, e.g. 1947:8 (period label, length)")
    parser.add_argument(
        "--K", type=int, default=None, help="number of spectra (default T)"
    )
    parser.add_argument(
        "--indicator", action="store_true", help="indicator constraints"
    )
    parser.add_argument(
        "--no-symmetry", action="store_true", help="no m_1 >= ... >= m_K"
    )
    parser.add_argument(
        "--start", action="store_true", help="add the hyperbola point as a start"
    )
    parser.add_argument(
        "--exact", action="store_true", help="branch and bound to optimality"
    )
    parser.add_argument(
        "--stall", type=int, default=5000, help="stall nodes (heuristic)"
    )
    parser.add_argument("--time", type=float, default=None, help="time limit, seconds")
    parser.add_argument("--denominator", type=int, default=10**6, help="rational check")
    parser.add_argument("--no-exact", action="store_true", help="skip the rho = 0 test")
    parser.add_argument("--verbose", action="store_true", help="show the SCIP log")
    args = parser.parse_args()
    if args.data is None and (args.P is None or args.y is None):
        parser.error("give --P and --y, or --data")

    problem = load(args)
    print(f"T={problem.T} d={problem.d}", end="  ")
    if problem.periods:
        print(f"periods {problem.periods[0]}..{problem.periods[-1]}", end="  ")
    print()
    if not args.no_exact and problem.T <= MAX_T:
        exact = weakly_solvable(problem)
        if exact.solvable:
            print("y is weakly solvable at P (certified): rho = 0")
            for S, mass in exact.masses.items():
                print(f"  m{{{','.join(str(t + 1) for t in sorted(S))}}} = {mass}")
            return
        if exact.solvable is False:
            lam = ", ".join(str(v) for v in exact.refutation)
            print(f"y is not weakly solvable at P (certified), refutation ({lam})")
    prep = prepare(problem)
    print(f"kappa={prep.kappa:.6g}  D={prep.D:.6g}")
    solution = solve(
        prep,
        K=args.K,
        indicator=args.indicator,
        symmetry=not args.no_symmetry,
        start=args.start,
        time_limit=args.time,
        verbose=args.verbose,
        exact=args.exact,
        stall_nodes=args.stall,
    )
    if not solution.spectra:
        print(f"status={solution.status}: no solution")
        return
    print(describe(solution, problem.periods, problem.factors))
    print(verify(problem, rational(solution, args.denominator)))


if __name__ == "__main__":
    main()
