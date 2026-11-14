#!/bin/bash
# CertiFFI per-file directive shim. Installed as bin/lean of the wrapped toolchain that
# tools/make-wrapped-toolchain.sh builds; see README "Build from source".
#
# A few export modules carry a source comment "Compile using EVAL_OPAQUE_CALLEES=<value>": they must be compiled
# with that environment variable set, or they elaborate differently. Lean has no per-file environment, so this shim
# applies the comment of the .lean file being compiled, then execs the real Lean 4.35.0 unchanged.
# - Only EVAL_OPAQUE_CALLEES is honoured; any other directive key is a hard error (exit 64).
# - Every inherited EVAL_* variable is cleared first, so no ambient value reaches any module.
# - A trailing "." on the value is stripped.
# The real Lean is $LEAN_REAL if set, else bin/lean.real beside this file (a link to the stock toolchain's lean).
# This shim is removed when the directive becomes a Lean option in source (next release train).
set -u
here=$(cd "$(dirname "$0")" && pwd)
REAL=${LEAN_REAL:-$here/lean.real}
[ -x "$REAL" ] || { echo "lean-wrapper: real lean not found at $REAL (set LEAN_REAL)" >&2; exit 127; }
for v in $(compgen -e | grep '^EVAL_' || true); do unset "$v"; done
for a in "$@"; do
  case "$a" in
    *.lean)
      if [ -f "$a" ]; then
        kv=$(grep -oE "Compile using [A-Z_]+=[^[:space:]]+" "$a" | head -1 | sed -e "s/^Compile using //" -e "s/\.$//")
        if [ -n "$kv" ]; then
          case "${kv%%=*}" in
            EVAL_OPAQUE_CALLEES) export "$kv" ;;
            *) echo "lean-wrapper: refusing directive key '${kv%%=*}' in $a (allowlist: EVAL_OPAQUE_CALLEES)" >&2; exit 64 ;;
          esac
        fi
      fi ;;
  esac
done
exec "$REAL" "$@"
