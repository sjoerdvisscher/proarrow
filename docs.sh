rm -rf docs
mkdir docs

cabal haddock \
  --haddock-hyperlink-source \
  --haddock-options="
    --comments-base=https://github.com/sjoerdvisscher/proarrow/
    --comments-module=https://github.com/sjoerdvisscher/proarrow/blob/main/src/%{MODULE/.//}.hs
    --comments-entity=https://github.com/sjoerdvisscher/proarrow/blob/main/src/%{MODULE/.//}.hs#L%L
    --pretty-html
    --odir=docs"
