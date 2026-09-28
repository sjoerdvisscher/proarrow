#!/usr/bin/env bash
set -euo pipefail

# Build the custom documentation with mkdocs.sh and upload it to Hackage.
#
#   bash hackage-docs.sh               upload to the package candidate
#   bash hackage-docs.sh --publish     upload to the published package
#   bash hackage-docs.sh --no-upload   only build the tarball
#
# Other arguments go to `cabal upload`. Without `-t`, `--token` or `-u` the API token is read
# from the macOS Keychain entry `hackage-token` (or HACKAGE_TOKEN_SERVICE), see below.
# The docs are built with GHC_VERSION (default 9.12, a version in tested-with), using ghcup's
# versioned ghc-X and haddock-X binaries, since haddock interfaces are tied to one GHC version.

: "${CABAL:=cabal}"
: "${GHC_VERSION:=9.12}"
export ARG_COMPILER="-w ghc-${GHC_VERSION}"
export HADDOCK="haddock-${GHC_VERSION}"
# On Hackage the docs live in <package page>/docs/, so ../ is the package page, which is the
# contents page Hackage users expect (for a candidate as well as a published version).
export USE_CONTENTS=../

cd "$(dirname "$0")"

upload=1
args=()
for arg in "$@"; do
  if [[ "$arg" == --no-upload ]]; then
    upload=
  else
    args+=("$arg")
  fi
done

version=$(awk '$1 == "version:" { print $2 }' proarrow.cabal)
name="proarrow-${version}-docs"

bash mkdocs.sh

# mkdocs.sh keeps going after a failed haddock run, so check that both libraries made it into the
# tree and into the combined contents page.
for f in proarrow.haddock testing.haddock index.html Proarrow.html Proarrow-Testing.html; do
  if [[ ! -f "docs/$f" ]]; then
    echo "mkdocs.sh did not produce docs/$f" >&2
    exit 1
  fi
done
if ! grep -q 'Proarrow-Testing.html' docs/index.html; then
  echo "docs/index.html does not list the proarrow:testing modules" >&2
  exit 1
fi

# Hackage wants a ustar tarball with a single top-level directory named <package>-<version>-docs.
# COPYFILE_DISABLE keeps macOS tar from adding ._ metadata files.
out=$(mktemp -d)
cp -R docs "${out}/${name}"
COPYFILE_DISABLE=1 tar -C "${out}" --format=ustar -czf "${out}/${name}.tar.gz" "${name}"
echo "Built ${out}/${name}.tar.gz"

if [[ -n "$upload" ]]; then
  # Unless credentials were given on the command line, use the Hackage API token stored in the
  # macOS Keychain (`security add-generic-password -a "$USER" -s hackage-token -w`), if there is
  # one; otherwise cabal asks for a username and password.
  if [[ " ${args[*]-} " != *" -t"* && " ${args[*]-} " != *" --token"* && " ${args[*]-} " != *" -u"* ]] \
    && token=$(security find-generic-password -s "${HACKAGE_TOKEN_SERVICE:-hackage-token}" -w 2>/dev/null); then
    args+=(--token="$token")
  fi
  ${CABAL} upload --documentation ${args[@]+"${args[@]}"} "${out}/${name}.tar.gz"
fi
