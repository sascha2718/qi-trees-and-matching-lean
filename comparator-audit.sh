#!/usr/bin/env bash
# Run the comparator audit of the headline theorems: the statements frozen in
# Challenge.lean, proved in Solution.lean, with the audited names listed in
# comparator.json.
#
# The judge is `lake comparator`, which ships in the pinned toolchain together
# with the kernels it replays through, so the audit needs no separately built
# verifier. It builds Challenge and Solution, compares their statements,
# enforces the permitted axioms, and replays the exported proofs through Lean's
# kernel and, under --paranoid, through every external checker the toolchain
# bundles.
#
# The judge builds and exports the project inside a `bwrap` sandbox: `/` is
# bound read-only, only `.lake` is writable, and the build, the export and the
# kernels run in an empty network namespace. `bubblewrap` is therefore
# required, and needs unprivileged user namespaces or to be installed setuid
# root; set COMPARATOR_BWRAP to select a particular binary. Ubuntu 24.04
# restricts unprivileged user namespaces by AppArmor, so the CI workflow builds
# the pinned bubblewrap release and loads a profile for it.
#
# The sandbox is what the verdict rests on, so this script does not offer to
# disable it. A host without bubblewrap cannot run the audit.
set -euo pipefail
cd "$(dirname "$0")"

bwrap_bin="${COMPARATOR_BWRAP:-bwrap}"
if ! command -v "$bwrap_bin" >/dev/null 2>&1; then
  echo "comparator-audit: bubblewrap ($bwrap_bin) is not available, so the audit cannot run." >&2
  echo "comparator-audit: run it on Linux with bubblewrap installed, or through" >&2
  echo "comparator-audit: .github/workflows/build.yml, which provisions the pinned release." >&2
  exit 2
fi

exec lake comparator --config comparator.json --paranoid
