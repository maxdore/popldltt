#!/usr/bin/env bash
# Checks the DLTT artefact:
#   1. reports the Agda version (the artefact was tested with 2.6.4.3),
#   2. scans the sources for unsafe features (postulates, holes, pragmas that
#      disable checks) and checks that all files use --safe,
#   3. removes interface files and typechecks DLTT/Everything.agda from scratch,
#   4. checks that this typechecked every .agda file (none is left out).
#
# Run from the artefact root:  ./scripts/check.sh   (or: make check)
# Set KEEP_INTERFACES=1 to skip removing interface files (faster re-runs).

set -u
cd "$(dirname "$0")/.."

AGDA="${AGDA:-agda}"
TESTED_VERSIONS="2.6.4.3 2.7.0.1 2.8.0 2.8.0.2"
# Files allowed to be checked without --safe (none).
UNSAFE_ALLOWED=""

fail=0
section() { printf '\n== %s\n' "$1"; }
ok()      { printf '  [ok]   %s\n' "$1"; }
warn()    { printf '  [warn] %s\n' "$1"; }
bad()     { printf '  [FAIL] %s\n' "$1"; fail=1; }
allowed() { case " $UNSAFE_ALLOWED " in *" $1 "*) return 0;; esac; return 1; }

files=$(find DLTT -name '*.agda' | LC_ALL=C sort)

section "Agda version"
if ! command -v "$AGDA" >/dev/null 2>&1; then
  bad "'$AGDA' not found on PATH (see README.md, Section 'Getting started')"
  exit 1
fi
version=$("$AGDA" --version | head -n 1)
tested=0
for v in $TESTED_VERSIONS; do
  # release binaries may append a commit hash, e.g. "2.8.0-3d04bac"
  case "$version" in "Agda version $v"|"Agda version $v-"*) tested=1 ;; esac
done
if [ "$tested" = 1 ]; then
  ok "$version"
else
  warn "$version (the artefact was tested with Agda $TESTED_VERSIONS)"
fi

section "Unsafe features"
for f in $files; do
  if head -n 5 "$f" | grep -Eq '\{-# OPTIONS .*--safe'; then
    ok "$f uses --safe"
  elif allowed "$f"; then
    warn "$f is not checked with --safe (expected, see README.md)"
  else
    bad "$f does not use --safe"
  fi
done
# Anything that weakens the guarantees of the typechecker. TERMINATING is
# rejected under --safe anyway.
pattern='postulate|\{!|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|INJECTIVE|REWRITE|--type-in-type|--allow-unsolved-metas|--allow-incomplete-matches|--rewriting|--no-termination-check|--no-positivity-check|primTrustMe'
hits=$(grep -nE "$pattern" $files || true)
if [ -n "$hits" ]; then
  bad "found unsafe constructs:"
  printf '%s\n' "$hits" | sed 's/^/         /'
else
  ok "no postulates, holes or check-disabling pragmas/flags"
fi
for f in $files; do
  n=$(grep -c '{-# TERMINATING #-}' "$f")
  [ "$n" -gt 0 ] && warn "$f: $n TERMINATING pragma(s) "
done

section "Typechecking DLTT/Everything.agda"
if [ "${KEEP_INTERFACES:-0}" != 1 ]; then
  rm -rf _build
  find DLTT -name '*.agdai' -delete
  ok "removed interface files"
fi
start=$(date +%s)
if "$AGDA" DLTT/Everything.agda; then
  ok "typechecked in $(( $(date +%s) - start ))s"
  typechecked=1
else
  bad "Agda reported an error"
  typechecked=0
fi

section "Every module was typechecked via DLTT/Everything.agda"
if [ "$typechecked" = 1 ]; then
  for f in $files; do
    i="${f%.agda}.agdai"
    if [ -f "$i" ] || find _build -path "*/$i" 2>/dev/null | grep -q .; then
      ok "$f"
    else
      bad "$f is not (transitively) imported by DLTT/Everything.agda"
    fi
  done
else
  warn "skipped since typechecking failed"
fi

section "Result"
if [ "$fail" = 0 ]; then
  echo "  ALL CHECKS PASSED"
else
  echo "  SOME CHECKS FAILED"
fi
exit "$fail"
