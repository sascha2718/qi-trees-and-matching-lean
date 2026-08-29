#!/usr/bin/env bash
# Run the comparator audit of the headline theorems: the statements frozen in
# Challenge.lean, proved in Solution.lean, with the audited names listed in
# comparator-config.json.
#
# Requires local builds of leanprover/comparator and of leanprover/lean4export
# at the project's Lean version (v4.32.2); override the default locations with
# COMPARATOR_TOOLS or the individual variables below. landrun is Linux-only,
# so on macOS comparator's shim is used and the builds run unsandboxed. To add
# the independent nanoda kernel, build it with cargo, set COMPARATOR_NANODA to
# the binary, and set "enable_nanoda": true in comparator-config.json.
set -euo pipefail
cd "$(dirname "$0")"
TOOLS="${COMPARATOR_TOOLS:-$HOME/Documents/lean}"
export COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$TOOLS/comparator/scripts/fake-landrun.sh}"
export COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$TOOLS/lean4export/.lake/build/bin/lean4export}"
exec lake env "$TOOLS/comparator/.lake/build/bin/comparator" comparator-config.json
