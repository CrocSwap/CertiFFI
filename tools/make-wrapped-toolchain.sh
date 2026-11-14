#!/bin/bash
# Build the CertiFFI wrapped toolchain and register it with elan.
# usage: tools/make-wrapped-toolchain.sh [DEST_DIR] [NAME]
#   NAME     elan toolchain name (default certiffi-wrapped-v4.35.0)
#   DEST_DIR where to build it (default ~/.local/share/certiffi/<NAME>)
# The result is stock leanprover/lean4:v4.35.0 with ONE change: bin/lean is tools/lean-wrapper.sh (the per-file
# directive shim) and the real compiler is bin/lean.real. Everything else links to the stock toolchain, except
# bin/lake, which is COPIED: Lake finds its toolchain (and so which `lean` to run) from its own executable path.
# Only building the export from source needs this; the prebuilt-cache path (get-cache.sh) does not.
set -euo pipefail
NAME=${2:-certiffi-wrapped-v4.35.0}
DEST=${1:-$HOME/.local/share/certiffi/$NAME}
STOCK=leanprover/lean4:v4.35.0
HERE=$(cd "$(dirname "$0")" && pwd)
command -v elan >/dev/null || { echo "make-wrapped-toolchain: elan not found on PATH" >&2; exit 2; }
elan toolchain install "$STOCK" >/dev/null 2>&1 || true
SYSROOT=$(elan run "$STOCK" lean --print-prefix)
[ -x "$SYSROOT/bin/lean" ] && [ -x "$SYSROOT/bin/lake" ] || { echo "make-wrapped-toolchain: no stock toolchain at $SYSROOT" >&2; exit 2; }
rm -rf "$DEST"; mkdir -p "$DEST/bin"
for e in "$SYSROOT"/*; do b=$(basename "$e"); [ "$b" = bin ] || ln -s "$e" "$DEST/$b"; done
for e in "$SYSROOT"/bin/*; do b=$(basename "$e"); case "$b" in lean|lake) ;; *) ln -s "$e" "$DEST/bin/$b" ;; esac; done
cp "$SYSROOT/bin/lake" "$DEST/bin/lake"
ln -s "$SYSROOT/bin/lean" "$DEST/bin/lean.real"
cp "$HERE/lean-wrapper.sh" "$DEST/bin/lean"; chmod 755 "$DEST/bin/lean"
elan toolchain link "$NAME" "$DEST"
echo "linked elan toolchain '$NAME' -> $DEST"
echo "build from source with:  lake +$NAME build"
