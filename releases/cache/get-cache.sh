#!/bin/bash
# CertiFFI consumer cache step (the analogue of `lake exe cache get`). Run once after `lake update`.
# Each archive is a `lake pack` tarball of a package's .lake/build. Every archive is checked against CACHE-SHA256.txt
# (pinned beside this script; at release, these values are published with the signed release) and REFUSED on any
# mismatch or missing entry. Then it is extracted straight into the dependency's build dir (not `lake unpack`, which
# loads each dependency as its own workspace and re-clones its git deps).
# TRUST: this path trusts whoever built the archives. Lean does not re-check proofs inside imported .olean files.
# See README.md for the independent paths.
# Usage: get-cache.sh ARCHIVE_DIR   (run in the consumer root, after `lake update`)
# WHICH archives: derived, not listed (D274, 7 packages). The consumer's lakefile.toml requires ONE release package R
# (override: CERTIFFI_PKG=R). Its sibling closure is read from the pinned export's own lakefiles under
# .lake/packages/R/<pkg>/lakefile.toml (`path = "../X"` requires), and the IsaWitness archives are named by the rev that
# Provider's lakefile pins. Every derived archive must then be in the signed manifest.
set -euo pipefail
A=${1:?archive dir}
R=${CERTIFFI_PKG:-$(awk -F'"' '/^\[\[require\]\]/{r=1; next} r && /^name *=/ {print $2; exit}' lakefile.toml)}
[[ "$R" =~ ^[A-Za-z0-9_]+$ ]] || { echo "REFUSED: cannot read the required package from lakefile.toml (got '$R')" >&2; exit 2; }
ROOT=.lake/packages/$R
[ -f "$ROOT/$R/lakefile.toml" ] || { echo "REFUSED: $ROOT/$R/lakefile.toml missing (run lake update first)" >&2; exit 2; }
M="$(dirname "$0")/CACHE-SHA256.txt"
[ -f "$M" ] || { echo "missing $M" >&2; exit 2; }
# The manifest itself must be signed by the release signer (dfc1): ssh-keygen -Y sign -n armcert-release-cache CACHE-SHA256.txt
# produces CACHE-SHA256.txt.sig; ALLOWED_SIGNERS defaults to the export's releases/allowed_signers.
# Trust anchor: confirm the release key fingerprint OUT OF BAND first (see README). No bypass exists in this script.
NS=armcert-release-cache   # distinct cache namespace (allowed_signers lists claim + cache)
SIG="$M.sig"; AS=${ALLOWED_SIGNERS:-$ROOT/releases/allowed_signers}
[ -f "$SIG" ] || { echo "REFUSED: $SIG missing (manifest must be signed by the release signer)" >&2; exit 4; }
[ -f "$AS" ] || { echo "REFUSED: allowed_signers not found at $AS" >&2; exit 4; }
P=$(awk 'NF && $1 !~ /^#/ {print $1; exit}' "$AS")
ssh-keygen -Y verify -f "$AS" -I "$P" -n "$NS" -s "$SIG" < "$M" >/dev/null 2>&1 \
  || { echo "REFUSED: $M signature does not verify against $AS (namespace $NS)" >&2; exit 4; }
sha() { if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d" " -f1; else shasum -a 256 "$1" | cut -d" " -f1; fi; }
# sibling closure of R (breadth-first over `path = "../X"` requires)
todo=("$R"); seen=" "
while [ ${#todo[@]} -gt 0 ]; do
  p=${todo[0]}; todo=("${todo[@]:1}")
  case "$seen" in *" $p "*) continue;; esac
  [[ "$p" =~ ^[A-Za-z0-9_]+$ ]] && [ -f "$ROOT/$p/lakefile.toml" ] || { echo "REFUSED: package '$p' not found under $ROOT" >&2; exit 2; }
  seen="$seen$p "
  for d in $(sed -nE 's#^path *= *"\.\./([A-Za-z0-9_]+)" *$#\1#p' "$ROOT/$p/lakefile.toml"); do todo+=("$d"); done
done
case "$seen" in *" Provider "*) ;; *) echo "REFUSED: Provider not in the closure of $R" >&2; exit 2;; esac
REV=$(sed -nE 's#^rev *= *"([0-9a-f]{40})" *$#\1#p' "$ROOT/Provider/lakefile.toml" | head -1)
[ -n "$REV" ] || { echo "REFUSED: no 40-hex IsaWitness rev in $ROOT/Provider/lakefile.toml" >&2; exit 2; }
PLAN=".lake/packages/ArmFull/model:isawitness-${REV:0:7}-model.tgz
.lake/packages/ArmFull/vendor/lean-sail:isawitness-${REV:0:7}-lean-sail.tgz"
for p in $seen; do PLAN="$PLAN
$ROOT/$p:certiffi-$p.tgz"; done
echo "plan for $R: ArmFull@${REV:0:7} +$seen" >&2
# 1) verify EVERY archive first; nothing is extracted unless all pass
while IFS=: read -r dir f; do
  want=$(awk -v f="$f" '$2==f {print $1}' "$M")
  [ -n "$want" ] || { echo "REFUSED: $f not in CACHE-SHA256.txt (nothing extracted)" >&2; exit 3; }
  [ "$(sha "$A/$f")" = "$want" ] || { echo "REFUSED: $f sha256 mismatch (nothing extracted)" >&2; exit 3; }
done <<< "$PLAN"
# 2) extract
while IFS=: read -r dir f; do mkdir -p "$dir/.lake/build" && tar -xzf "$A/$f" -C "$dir/.lake/build"; done <<< "$PLAN"
echo "cache verified (sha256) and extracted"
