"""Command line for the minimal perturbation problem.

python code/perturb.py --P "4,1;3,3;1,4" --y "1,5,3"
python code/perturb.py --P "4,1;3,3;1,4" --y "1,5,3" --indicator --verbose
python code/perturb.py --P "1,3;2,2;3,1;2,3" --y "2,1,1,1" --K 3 --time 60

Prints the chosen parameters, the solver value (rho(P, y) once the status is optimal),
and the exact check of the answer converted to rationals with the given denominator.
"""

import argparse

from perturbation import Problem, prepare, rational, solve, verify


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--P", required=True, help='prices, rows by ";", e.g. "4,1;3,3;1,4"'
    )
    parser.add_argument("--y", required=True, help='outputs, e.g. "1,5,3"')
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
        "--no-start", action="store_true", help="no hyperbola start point"
    )
    parser.add_argument("--time", type=float, default=None, help="time limit, seconds")
    parser.add_argument(
        "--denominator", type=int, default=10**6, help="for the rational conversion"
    )
    parser.add_argument("--verbose", action="store_true", help="show the SCIP log")
    args = parser.parse_args()

    problem = Problem.parse(args.P, args.y)
    prep = prepare(problem)
    print(f"T={problem.T} d={problem.d}  kappa={prep.kappa:.6g}  D={prep.D:.6g}")
    solution = solve(
        prep,
        K=args.K,
        indicator=args.indicator,
        symmetry=not args.no_symmetry,
        start=not args.no_start,
        time_limit=args.time,
        verbose=args.verbose,
    )
    print(
        f"status={solution.status}  value={solution.value:.6g}  "
        f"bound={solution.bound:.6g}  time={solution.seconds:.2f}s"
    )
    if solution.spectra:
        print(verify(problem, rational(solution, args.denominator)))


if __name__ == "__main__":
    main()
