#!/usr/bin/env bash
set -euo pipefail

# Search project Lean sources, excluding Lake's downloaded dependencies.
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

mapfile -t files < <(find . -name '*.lean' -not -path './.lake/*' | sort)

if [[ ${#files[@]} -eq 0 ]]; then
  echo "check_no_sorry: no project .lean files found" >&2
  exit 1
fi

fail=0

if grep -n -E -H --binary-files=without-match '\bsorry\b' "${files[@]}"; then
  echo "check_no_sorry: found 'sorry' in project Lean sources" >&2
  fail=1
fi

if grep -n -E -H --binary-files=without-match '\badmit\b' "${files[@]}"; then
  echo "check_no_sorry: found 'admit' in project Lean sources" >&2
  fail=1
fi

if grep -n -E -H --binary-files=without-match '(^|[[:space:]])axiom[[:space:]]' "${files[@]}"; then
  echo "check_no_sorry: found a custom axiom declaration in project Lean sources" >&2
  fail=1
fi

if [[ "$fail" -ne 0 ]]; then
  exit 1
fi

echo "check_no_sorry: no sorry, admit, or custom axiom declarations in project sources"
