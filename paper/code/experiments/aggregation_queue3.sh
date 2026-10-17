#!/bin/zsh
# Controls for "the remaining correction sits on pII" (one solver process at a time; run from paper/code):
#   nohup zsh experiments/aggregation_queue3.sh > experiments/results/queue3.log 2>&1 &
# 1. d = 8 with the move of pII weighted 100x: if OPT_1 rises several-fold and the moves go to the detailed
#    types, pII is the cheap place to repair the data.
# 2. d = 7, the seven detailed prices / pGO without a pII coordinate: are the data nearly solvable without pII?
set -u
cd "$(dirname "$0")/.."
PY="$(cd ../.. && pwd)/.venv/bin/python"
echo "queue3 start $(date)"
nice -n 19 $PY experiments/aggregation_lp.py wii 24 1 27 46 49 15 12 --time-limit 900
nice -n 19 $PY experiments/aggregation_lp.py d7go 24 1 27 46 49 15 12 --time-limit 900
echo "queue3 end $(date)"
$PY experiments/aggregation_lp.py table
$PY experiments/aggregation_lp.py moves
