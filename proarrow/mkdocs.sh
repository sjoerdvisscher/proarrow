: "${CABAL:=cabal}"
: "${HADDOCK:=haddock}"
: "${ARG_COMPILER:=}"
# Where the "Contents" link at the top of each page goes. Empty means the index.html generated
# below (GitHub Pages); hackage-docs.sh sets it to ../, Hackage's own package page.
: "${USE_CONTENTS:=}"

# The optics lattice diagram (Proarrow.Optics) is generated from lattice.dot:
#   dot -Tsvg lattice.dot -o lattice.svg
rm -rf docs
mkdir docs
# copy the optics lattice image next to the module HTML so Haddock's <<lattice.svg>> resolves
cp lattice.svg docs/

# Both libraries render into one doc tree (Hackage has a single documentation set per package).
# This is hand-rolled rather than `cabal haddock-project` because that documents the whole
# project (proarrow-equipment included), nests pages per component (breaking published URLs and
# the flat tree `cabal upload --documentation` expects). One invocation renders each library
# once; the source-link template names src/, and the testing modules are pointed at testing/
# below, where the per-entity links are corrected anyway.
${CABAL} haddock lib:proarrow lib:testing ${ARG_COMPILER} \
  --haddock-hyperlink-source \
  --haddock-html-location='https://hackage.haskell.org/package/$pkg-$version/docs' \
  --haddock-options="
    --comments-base=https://github.com/sjoerdvisscher/proarrow/
    --comments-module=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/src/%{MODULE/.//}.hs
    --comments-entity=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/src/%{MODULE/.//}.hs#L%L
    --pretty-html
    ${USE_CONTENTS:+--use-contents=${USE_CONTENTS}}
    --odir=docs"

# cabal writes the haddock interface of each library into its build directory; the newest ones
# are from the run above
version=$(awk '$1 == "version:" { print $2 }' proarrow.cabal)
main_iface=$(ls -t $(find ../dist-newstyle/build -path "*/proarrow-${version}/doc/*" -name proarrow.haddock) | head -1)
testing_iface=$(ls -t $(find ../dist-newstyle/build -path "*/proarrow-${version}/l/testing/*" -name testing.haddock) | head -1)
cp "$main_iface" docs/proarrow.haddock
cp "$testing_iface" docs/testing.haddock

# regenerate the contents and index pages covering both libraries
${HADDOCK} --gen-contents --gen-index -o docs --title=proarrow ${USE_CONTENTS:+--use-contents=${USE_CONTENTS}} \
  --read-interface=,docs/proarrow.haddock \
  --read-interface=,docs/testing.haddock

# the testing modules live under testing/, not src/
grep -rl 'proarrow/src/Proarrow/Testing' docs | xargs perl -pi -e 's|proarrow/src/(Proarrow/Testing[^"]*\.hs)|proarrow/testing/$1|g'

# the testing pages link to the main library's modules via hackage; make those links local
grep -rl 'hackage.haskell.org/package/proarrow-' docs | xargs perl -pi -e 's|https://hackage.haskell.org/package/proarrow-[0-9.]+/docs/||g'

grep -rilE '>(User )?Comments<' docs | xargs perl -pi -e 's/>(User )?Comments</>Github</gi'

# haddock's --comments-entity links use the page's module and the enclosing declaration's line;
# make each one agree with the Source link beside it
python3 fix-github-links.py docs https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/
