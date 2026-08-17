#!/usr/bin/env bash
set -euo pipefail

: "${CABAL:=cabal}"
: "${ARG_COMPILER:=}"

# Build the library normally first. Dependencies must not be built with doctest
# standing in for the compiler.
${CABAL} build ${ARG_COMPILER} lib:proarrow

# doctest loads every exposed module and checks each >>> example against the
# expected output on the lines below it. Running it through `cabal repl` means
# cabal supplies the dependencies and the package's own GHC options -- GHC2024
# and the long default-extensions list -- which doctest would otherwise need to
# be told about by hand.
${CABAL} repl ${ARG_COMPILER} lib:proarrow --with-compiler=doctest
