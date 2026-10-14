#!/bin/sh
# Creates a local virtual environment, installs gurobipy and numpy, runs all instances.
# After each instance one line is appended to results.jsonl.
set -e
cd "$(dirname "$0")"
python3 -m venv .venv
.venv/bin/pip install --quiet --upgrade pip
.venv/bin/pip install --quiet -r requirements.txt
.venv/bin/python rho_gurobi.py instances.json --out results.jsonl "$@"
