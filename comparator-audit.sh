#!/usr/bin/env bash
# Run the comparator audit of the headline theorems: the statements frozen in
# Challenge.lean, proved in Solution.lean, with the audited names listed in
# comparator.json.
#
# Local development runner. Requires local builds of leanprover/comparator and
# leanprover/lean4export, with lean4export matching the project's Lean version;
# override the default locations with COMPARATOR_TOOLS or the variables below.
# On Linux this uses real landrun. On macOS the development shim runs builds
# without sandboxing. The fresh CI audit has additional systemd restrictions.
# To add the independent nanoda kernel, build it with cargo, set COMPARATOR_NANODA to
# the binary, and set "enable_nanoda": true in comparator.json.
set -euo pipefail
cd "$(dirname "$0")"
TOOLS="${COMPARATOR_TOOLS:-$HOME/Documents/lean}"
if [[ -z "${COMPARATOR_LANDRUN:-}" ]]; then
  if [[ "$(uname -s)" == Darwin ]]; then
    export COMPARATOR_LANDRUN="$TOOLS/comparator/scripts/fake-landrun.sh"
  else
    export COMPARATOR_LANDRUN=landrun
  fi
fi
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$TOOLS/lean4export/.lake/build/bin/lean4export}"
exec lake env "$TOOLS/comparator/.lake/build/bin/comparator" comparator.json
