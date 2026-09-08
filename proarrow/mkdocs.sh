: "${CABAL:=cabal}"
: "${HADDOCK:=haddock}"
: "${ARG_COMPILER:=}"

# lattice.dot is the Graphviz source of the optics subtyping lattice; the ASCII diagram in
# Proarrow.Optics is drawn after its rendering:  dot -Tsvg lattice.dot -o lattice.svg
rm -rf docs
mkdir docs

# Both libraries render into one doc tree (Hackage has a single documentation set per package).
# This is hand-rolled rather than `cabal haddock-project` because that documents the whole
# project (proarrow-equipment included), nests pages per component (breaking published URLs and
# the flat tree `cabal upload --documentation` expects), and has no per-component haddock options
# (the --comments-module source template differs between src/ and testing/).
# The testing sublibrary goes first: its dependency pass re-renders the main library with the
# wrong source-link template, and the main run afterwards overwrites those pages correctly.
${CABAL} haddock lib:testing ${ARG_COMPILER} \
  --haddock-hyperlink-source \
  --haddock-html-location='https://hackage.haskell.org/package/$pkg-$version/docs' \
  --haddock-options="
    --comments-base=https://github.com/sjoerdvisscher/proarrow/
    --comments-module=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/testing/%{MODULE/.//}.hs
    --comments-entity=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/testing/%{MODULE/.//}.hs#L%L
    --pretty-html
    --odir=docs
    --dump-interface=docs/testing.haddock"

${CABAL} haddock lib:proarrow ${ARG_COMPILER} \
  --haddock-hyperlink-source \
  --haddock-html-location='https://hackage.haskell.org/package/$pkg-$version/docs' \
  --haddock-options="
    --comments-base=https://github.com/sjoerdvisscher/proarrow/
    --comments-module=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/src/%{MODULE/.//}.hs
    --comments-entity=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/src/%{MODULE/.//}.hs#L%L
    --pretty-html
    --odir=docs
    --dump-interface=docs/proarrow.haddock"

# regenerate the contents and index pages covering both libraries
${HADDOCK} --gen-contents --gen-index -o docs --title=proarrow \
  --read-interface=,docs/proarrow.haddock \
  --read-interface=,docs/testing.haddock

# the testing pages link to the main library's modules via hackage; make those links local
grep -rl 'hackage.haskell.org/package/proarrow-' docs | xargs sed -i -E 's|https://hackage.haskell.org/package/proarrow-[0-9.]+/docs/||g'

grep -rilE '>(User )?Comments<' docs | xargs sed -i -E 's/>(User )?Comments</>Github</gI'
