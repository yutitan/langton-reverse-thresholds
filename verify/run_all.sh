#!/usr/bin/env bash
# Quick checks: no Lean, no upstream checkout required.
set -eo pipefail
cd "$(dirname "$0")"

echo "== 1/7 88-step and 11-cell diagnosis =="
python3 ant_gate_diagnosis.py

echo
echo "== 2/7 14-cell ordered witness and the 12K+2 family =="
python3 ant_gate_ordered.py

echo
echo "== 3/7 bounded preparation minima (12K+6) =="
python3 ant_gate_bounded.py

echo
echo "== 4/7 supply constants =="
python3 ant208_flux.py

echo
echo "== 5/7 20-cell / 12K-5 construction =="
python3 ant208_extend.py

echo
echo "== 6/7 independent checks (self-contained, does not import the above) =="
python3 dsh_independent_checks.py

echo
echo "== 7/7 optional 22-ray table (set UPSTREAM to enable) =="
if [ -n "$UPSTREAM" ] && [ -f "$UPSTREAM/lean/TwoBlack/Level1Data.lean" ]; then
  python3 ant_ray_thresholds.py "$UPSTREAM/lean/TwoBlack/Level1Data.lean"
else
  echo "skip: set UPSTREAM=/path/to/langton-two-black (commit 95e896e...) to check the 22-ray table"
fi

echo
echo "ALL QUICK CHECKS PASSED"
