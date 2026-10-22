#!/usr/bin/env bash
# Extract the spike crate to Lean with Charon and Aeneas, then build it.
# Expects Charon and Aeneas checked out (and built) next to this repository:
#   ../charon (at the commit in ../aeneas/charon-pin), ../aeneas.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tools="$(cd "$here/../../.." && pwd)"
out="$here/out"
mkdir -p "$out"
(cd "$here/rust" && "$tools/charon/bin/charon" cargo --preset=aeneas --dest-file "$out/samplers.llbc")
rm -rf "$out/lean"
"$tools/aeneas/bin/aeneas" -backend lean -dest "$out/lean" -split-files -no-progress-bar "$out/samplers.llbc"
cp "$out/lean/Types.lean" "$out/lean/Funs.lean" "$here/lean/Samplers/"
# The external definitions (dashu) are left as the generated axioms.
cp "$out/lean/TypesExternal_Template.lean" "$here/lean/Samplers/TypesExternal.lean"
cp "$out/lean/FunsExternal_Template.lean" "$here/lean/Samplers/FunsExternal.lean"
printf 'module\npublic import Samplers.Funs\n' > "$here/lean/Samplers.lean"
(cd "$here/lean" && lake build && lake build Samplers.Tape)
