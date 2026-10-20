#!/bin/bash

# Verify the `opendp` crate with Creusot.
#
# Requires a Creusot installation (https://github.com/creusot-rs/creusot) and a
# checkout of OpenDP's fork of `creusot-std`, which adds `DeepModel` impls for
# `dashu` types. Point CREUSOT_STD_PATH at the fork's `creusot-std` directory.
#
# Usage: tools/creusot.sh [CARGO CREUSOT ARGS...]
#   e.g. tools/creusot.sh transformations::sum::*

# exit immediately upon failure, unset vars
set -e -u

: "${CREUSOT_STD_PATH:?set CREUSOT_STD_PATH to the forked creusot-std directory}"

cd "$(dirname "$0")/../rust"

# The fork is patched in on the command line rather than in Cargo.toml,
# so that normal builds never need the fork to be present.
exec cargo creusot "$@" -- \
  --no-default-features \
  --features "contrib,creusot-std/dashu" \
  --config "patch.crates-io.creusot-std.path=\"$CREUSOT_STD_PATH\""
