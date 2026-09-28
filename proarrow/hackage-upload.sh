#!/usr/bin/env bash
set -euo pipefail

# Upload the package to Hackage, then its custom documentation (hackage-docs.sh).
#
#   bash hackage-upload.sh                 upload as a package candidate
#   bash hackage-upload.sh --publish       publish (permanent, asks for confirmation)
#   bash hackage-upload.sh --publish --allow-dirty   publish with uncommitted changes in proarrow/
#
# A candidate upload packs the working tree as it is; only publishing insists on a clean tree.
#
# The API token is read from the macOS Keychain entry `hackage-token` (or HACKAGE_TOKEN_SERVICE),
# stored with `security add-generic-password -a "$USER" -s hackage-token -w`.

: "${CABAL:=cabal}"

cd "$(dirname "$0")"

publish=()
dirty_ok=
for arg in "$@"; do
  case "$arg" in
    --publish) publish=(--publish) ;;
    --allow-dirty) dirty_ok=1 ;;
    *)
      echo "unknown argument: $arg" >&2
      exit 1
      ;;
  esac
done

version=$(awk '$1 == "version:" { print $2 }' proarrow.cabal)

# cabal sdist packs the working tree as it is, so refuse to publish uncommitted changes.
if [[ ${#publish[@]} -gt 0 && -z "$dirty_ok" && -n "$(git status --porcelain -- .)" ]]; then
  echo "proarrow/ has uncommitted changes (use --allow-dirty to publish anyway):" >&2
  git status --short -- . >&2
  exit 1
fi

if ! token=$(security find-generic-password -s "${HACKAGE_TOKEN_SERVICE:-hackage-token}" -w 2>/dev/null); then
  echo "no Hackage token in the Keychain entry ${HACKAGE_TOKEN_SERVICE:-hackage-token}" >&2
  exit 1
fi

if [[ ${#publish[@]} -gt 0 ]]; then
  read -r -p "Publishing proarrow-${version} on Hackage is permanent. Continue? [y/N] " answer
  [[ "$answer" == [yY] ]] || exit 1
fi

out=$(mktemp -d)
${CABAL} sdist -o "${out}"
${CABAL} upload ${publish[@]+"${publish[@]}"} --token="$token" "${out}/proarrow-${version}.tar.gz"

bash hackage-docs.sh ${publish[@]+"${publish[@]}"} --token="$token"
