#!/usr/bin/env bash
# Extract OpenDP's samplers to Lean with Charon and Aeneas (`lean/Opendp/{Types,Funs}.lean`).
#
#   extract.sh          regenerate the files
#   extract.sh --check  fail if the committed files differ from a fresh extraction, that is, if
#                       the Rust code changed without the Lean being updated and re-proved
#
# Expects Charon and Aeneas built next to this repository: `../aeneas` (at commit fdebf20) and
# `../charon` (at the commit in `../aeneas/charon-pin`, de8736f).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
tools="$(cd "$repo/.." && pwd)"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT

# The functions to extract, with everything they call.
start_from=(
  crate::traits::samplers::cks20::sample_discrete_laplace_with
)
args=()
for f in "${start_from[@]}"; do args+=(--start-from "$f"); done

(cd "$repo/rust" && "$tools/charon/bin/charon" cargo --preset=aeneas "${args[@]}" \
  --dest-file "$out/opendp.llbc" -- -p opendp --lib --no-default-features \
  --target-dir "$tools/charon-opendp-target") >&2
"$tools/aeneas/bin/aeneas" -backend lean -dest "$out/lean" -split-files -no-progress-bar \
  -abort-on-error "$out/opendp.llbc" >&2

if [[ "${1:-}" == "--check" ]]; then
  status=0
  for f in Types Funs; do
    diff -u "$here/lean/Opendp/$f.lean" "$out/lean/$f.lean" || status=1
  done
  # Every external item the extracted code uses must have a hand-written model.
  for f in TypesExternal FunsExternal; do
    missing="$(comm -23 \
      <(grep -o '^axiom [^ ]*' "$out/lean/${f}_Template.lean" | sed 's/^axiom //' | sort) \
      <(grep -o '^\(def\|abbrev\) [^ ]*' "$here/lean/Opendp/$f.lean" | sed 's/^[a-z]* //' | sort))"
    if [[ -n "$missing" ]]; then
      echo "lean/Opendp/$f.lean has no model of: $missing" >&2
      status=1
    fi
  done
  exit $status
fi
cp "$out/lean/Types.lean" "$out/lean/Funs.lean" "$here/lean/Opendp/"
