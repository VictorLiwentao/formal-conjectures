#!/usr/bin/env bash
set -euo pipefail
worker_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(git -C "$worker_dir" rev-parse --show-toplevel)
runtime="$worker_dir/cache/runtime"
cd "$repo_root"
export LEAN_NUM_THREADS=2
export LEAN_PATH="$repo_root${LEAN_PATH:+:$LEAN_PATH}"
python3 research/batches/b01/control/check_assignments.py --repo "$repo_root" --worker codex-02 --against 238f78bdd5701ae4c97a0d70d4e22e2d45770d7a
lake --dir "$runtime" --wfail build 'FormalConjectures.OEIS.«3161»' 'FormalConjectures.OEIS.«3162»'
for target in A003161 A003162; do
  file="$worker_dir/targets/$target/$target"
  lake --dir "$runtime" env lean -DwarningAsError=true -o "$file.olean" "$file.lean"
done
lake --dir "$runtime" env lean -DwarningAsError=true "$worker_dir/ExactTypeAudit.lean"
