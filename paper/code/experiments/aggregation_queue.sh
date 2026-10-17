#!/bin/zsh
# Sequential queue of solver runs for the aggregation study (one solver process at a time).
# Run from paper/code:  nohup zsh experiments/aggregation_queue.sh > experiments/results/queue.log 2>&1 &
#
# 1. re-solve the cells that were optimal in the 600 s runs, now saving Q and the moved coordinates
# 2. the five near-converged time-limited cells with a 1800 s limit
set -u
cd "$(dirname "$0")/.."
PY="$(cd ../.. && pwd)/.venv/bin/python"
R=experiments/results
echo "queue start $(date)"

echo "== re-solve optimal cells (save Q)"
nice -n 19 $PY experiments/aggregation_lp.py real 15 12 27 46 49 --dims 8
nice -n 19 $PY experiments/aggregation_lp.py real 24 1 --dims 2,3,8
nice -n 19 $PY experiments/aggregation_lp.py real 31 --dims 3
nice -n 19 $PY experiments/aggregation_lp.py real 6 46 --dims 2

echo "== near-converged cells, 1800 s"
nice -n 19 $PY experiments/aggregation_lp.py real 46 --dims 3 --time-limit 1800
nice -n 19 $PY experiments/aggregation_lp.py real 31 --dims 2 --time-limit 1800
nice -n 19 $PY experiments/aggregation_lp.py real 15 --dims 2,3 --time-limit 1800
nice -n 19 $PY experiments/aggregation_lp.py real 27 --dims 3 --time-limit 1800

echo "queue end $(date)"
$PY experiments/aggregation_lp.py table
$PY experiments/aggregation_lp.py moves
