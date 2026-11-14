#!/bin/bash
# Checks that the 10 modules carrying a "Compile using EVAL_OPAQUE_CALLEES=..." directive were built WITH the directive
# (see README, "Building from source"). Run from the repository root after building, with the stock or wrapped toolchain:
#   tools/check-directive.sh
# For each module it lists every stored constant (tools/check-directive.lean), hashes the listing with SHA-256 and compares
# it with tools/DIRECTIVE-MODULES.sha256 (computed from the published cache, which was built with the directive).
# The check does not depend on where you built or on the Lake package name. Exit status 1 on any mismatch or missing module.
set -uo pipefail
cd "$(dirname "$0")/.."
sha() { if command -v sha256sum >/dev/null; then sha256sum | cut -d' ' -f1; else shasum -a 256 | cut -d' ' -f1; fi; }
rc=0
while read -r want pkg mod; do
  [ -z "$want" ] || [ "${want#\#}" != "$want" ] && continue
  o="$pkg/.lake/build/lib/lean/${mod//.//}.olean"
  if [ ! -f "$o" ]; then echo "MISSING  $pkg $mod ($o not built)"; rc=1; continue; fi
  got=$( (cd "$pkg" && lake env lean --run ../tools/check-directive.lean "../$o") | sha)
  if [ "$got" = "$want" ]; then echo "OK       $pkg $mod"; else echo "MISMATCH $pkg $mod (built without the directive?)"; rc=1; fi
done < tools/DIRECTIVE-MODULES.sha256
exit $rc
