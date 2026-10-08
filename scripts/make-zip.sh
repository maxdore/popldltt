#!/usr/bin/env bash
# Builds a clean archive of the artefact for upload to Zenodo.
#
#   ./scripts/make-zip.sh [VERSION]     (or: make zip VERSION=...)
#
# Only the files listed below are copied (no interface files, editor or OS
# junk). The staged copy is then checked from scratch with scripts/check.sh,
# the HTML rendering is generated into it, and it is zipped to
# dist/DLTT-artefact-VERSION.zip.

set -eu
cd "$(dirname "$0")/.."

VERSION="${1:-$(date +%Y-%m-%d)}"
NAME="DLTT-artefact-$VERSION"
AGDA="${AGDA:-agda}"

for f in README.md DLTT.agda-lib Makefile scripts/check.sh scripts/make-zip.sh; do
  [ -f "$f" ] || { echo "missing $f" >&2; exit 1; }
done
[ -f LICENSE ] || echo "warning: no LICENSE file; an open-source licence is needed for the Reusable badge" >&2

stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
dest="$stage/$NAME"
mkdir -p "$dest/scripts"

cp README.md DLTT.agda-lib Makefile "$dest/"
[ -f LICENSE ] && cp LICENSE "$dest/"
cp scripts/check.sh scripts/make-zip.sh "$dest/scripts/"
find DLTT -name '*.agda' | while read -r f; do
  mkdir -p "$dest/$(dirname "$f")"
  cp "$f" "$dest/$f"
done

echo "== Checking the staged copy"
( cd "$dest" && AGDA="$AGDA" ./scripts/check.sh )

echo "== Generating HTML"
( cd "$dest" && "$AGDA" --html --html-dir=html DLTT/Everything.agda >/dev/null )

# Remove build products of the check before packaging
rm -rf "$dest/_build"
find "$dest" \( -name '*.agdai' -o -name '.DS_Store' \) -delete

mkdir -p dist
out="$PWD/dist/$NAME.zip"
rm -f "$out"
( cd "$stage" && COPYFILE_DISABLE=1 zip -qrX "$out" "$NAME" )

echo "== Wrote $out"
unzip -l "$out" | grep -v '/html/' | tail -n +4
echo "   (plus $(unzip -l "$out" | grep -c '/html/.*\.html') HTML pages under html/)"
