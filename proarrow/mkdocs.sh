: "${CABAL:=cabal}"
: "${ARG_COMPILER:=}"

# lattice.dot is the Graphviz source of the optics subtyping lattice; the ASCII diagram in
# Proarrow.Optics is drawn after its rendering:  dot -Tsvg lattice.dot -o lattice.svg
rm -rf docs
mkdir docs

${CABAL} haddock ${ARG_COMPILER} \
  --haddock-hyperlink-source \
  --haddock-options="
    --comments-base=https://github.com/sjoerdvisscher/proarrow/
    --comments-module=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/src/%{MODULE/.//}.hs
    --comments-entity=https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/src/%{MODULE/.//}.hs#L%L
    --pretty-html
    --odir=docs"

grep -rilE '>(User )?Comments<' docs | xargs sed -i -E 's/>(User )?Comments</>Github</gI'
