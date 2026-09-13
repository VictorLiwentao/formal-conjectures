#!/usr/bin/env bash
# Copyright 2026 Wentao Li. Apache-2.0. AI assistance: OpenAI Codex.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS=2
export PYTHONDONTWRITEBYTECODE=1
worker=research/batches/b01/workers/codex-01
target="$worker/targets/A079727"
seed=238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
python3 research/batches/b01/control/check_assignments.py --repo . --worker codex-01 --against "$seed" > "$worker/assignment_check.log"
lake --wfail build 'FormalConjectures.OEIS.«79727»' > "$target/build.log" 2>&1
outdir=".lake/build/lib/lean/$target"
mkdir -p "$outdir"
compile() {
  lake env lean -DwarningAsError=true -o "$outdir/$1.olean" "$target/$1.lean" > "$target/$2.log" 2>&1
}
compile A079727 lean
compile Reductions reductions
compile Bilinear bilinear
compile PolynomialKernel polynomial_kernel
compile BlockSummation block_summation
compile ProductReduction product_reduction
compile PowerSeriesCoefficients power_series_coefficients
compile ExactTypeAudit exact_type_audit
python3 "$target/experiments.py" --bound 503 > "$target/experiments.jsonl"
python3 "$target/polynomial_screen.py" > "$target/polynomial_screen.jsonl"
python3 "$target/legendre_screen.py" --bound 101 > "$target/legendre_screen.jsonl"
python3 "$target/validate_experiments.py" > "$target/experiment_validation.log"
python3 - "$target" <<'PY'
import re, sys
from pathlib import Path
root = Path(sys.argv[1])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
logs = ['lean', 'reductions', 'bilinear', 'polynomial_kernel', 'block_summation',
        'product_reduction', 'power_series_coefficients', 'exact_type_audit']
count = 0
for name in logs:
    log = (root/(name+'.log')).read_text()
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    assert matches, name
    for declaration, axioms in matches:
        found = {a.strip() for a in axioms.split(',') if a.strip()}
        assert found <= allowed, (declaration, found)
        count += 1
    assert 'error:' not in log and 'warning:' not in log, name
for path in root.glob('*.lean'):
    code = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|axiom|native_decide)\b|Lean\.trustCompiler', code), path
print(f'PASS: {count} printed dependency closures use only the allowed axioms.')
PY
