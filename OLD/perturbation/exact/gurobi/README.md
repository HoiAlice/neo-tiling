# Minimal price perturbation: Gurobi run

Please run this on a machine with a full (e.g. academic) Gurobi license and send back the
file `results.jsonl`.

## Run

```sh
./run.sh
```

This creates `.venv/` here, installs `gurobipy` and `numpy` (Python 3.9+), and solves all
instances in `instances.json` one after another. The license is picked up the usual way
(`~/gurobi.lic` or `GRB_LICENSE_FILE`). The pip "restricted license" is NOT enough: the
models exceed 2000 variables.

After each instance one line (a JSON record: bounds, history, certificate) is appended to
`results.jsonl`, so an interrupted run keeps the instances finished so far. Expected time: the small
instances take seconds; each of the 9 large ones stops after `--budget` seconds (default
15 min), so the full run takes about 2.5 hours.

Options (passed through `./run.sh ...`):

| option | default | meaning |
|---|---|---|
| `--names A B` | all | run only these instances |
| `--budget S` | 900 | seconds per instance (no MILP runs past it) |
| `--time S` | 300 | time limit of one MILP |
| `--threads N` | 0 (all cores) | Gurobi threads |
| `--mem GB` | 8 | Gurobi SoftMemLimit per model |

For a quick check first: `./run.sh --names triangle rand_T4_d2_s3 rand_T4_d2_s5`
(takes seconds; expected values 1/3, 3/4, 5/8).

## What it computes

rho_1(P, y) = min sum_{t,i} |q_t^i / p_t^i - 1| over Q >= 0 such that y is weakly solvable at
Q. The script alternates a lower MILP master (a relaxation, its bound is a valid lower
bound), an oracle and an upper MILP master (certified upper bounds), and refines a
partition of the witness simplex until the bounds meet. See the docstring of
`rho_gurobi.py`.
