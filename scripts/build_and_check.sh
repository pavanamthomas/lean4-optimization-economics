#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export PATH="${HOME}/.elan/bin:${PATH}"

echo "== Lean toolchain =="
if [[ -f lean-toolchain ]]; then
  cat lean-toolchain
else
  echo "missing lean-toolchain" >&2
  exit 1
fi

echo
echo "== lake --version =="
lake --version

echo
echo "== lean --version =="
lean --version

echo
echo "== mathlib pin =="
if [[ -f lake-manifest.json ]]; then
  python3 - <<'PY'
import json
from pathlib import Path
data = json.loads(Path("lake-manifest.json").read_text())
pkgs = data.get("packages", data if isinstance(data, list) else [])
found = False
for p in pkgs:
    name = p.get("name") or p.get("name?")
    if name == "mathlib":
        print("name:", name)
        for k in ("rev", "inputRev", "url", "inherited"):
            if k in p:
                print(f"{k}:", p[k])
        found = True
if not found:
    raise SystemExit("mathlib entry not found in lake-manifest.json")
PY
else
  echo "missing lake-manifest.json" >&2
  exit 1
fi

echo
echo "== no-sorry / no-admit / no-custom-axiom =="
bash scripts/check_no_sorry.sh

echo
echo "== lake build =="
lake build
