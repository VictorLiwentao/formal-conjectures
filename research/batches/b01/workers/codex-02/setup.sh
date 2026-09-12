#!/usr/bin/env bash
set -euo pipefail
worker_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(git -C "$worker_dir" rev-parse --show-toplevel)
if [[ $# -ne 1 || ! -d "$1/packages" ]]; then
  echo 'Usage: setup.sh /path/to/compatible/.lake' >&2
  exit 1
fi
cache_source=$(cd "$1" && pwd)
runtime="$worker_dir/cache/runtime"
mkdir -p "$runtime"
if [[ -e "$runtime/.lake" ]]; then
  echo 'Private cache already exists; refusing to overwrite it.' >&2
  exit 1
fi
for file in lakefile.toml lake-manifest.json lean-toolchain; do
  cp "$repo_root/$file" "$runtime/$file"
done
for entry in FormalConjectures FormalConjecturesForMathlib FormalConjecturesUtil FormalConjecturesUtil.lean FormalConjecturesForMathlib.lean; do
  if [[ ! -e "$runtime/$entry" && ! -L "$runtime/$entry" ]]; then
    ln -s "$repo_root/$entry" "$runtime/$entry"
  fi
done
if [[ $(uname -s) == Darwin ]]; then
  cp -cR "$cache_source" "$runtime/.lake"
else
  cp -a "$cache_source" "$runtime/.lake"
fi
printf 'Private runtime: %s\n' "$runtime"
