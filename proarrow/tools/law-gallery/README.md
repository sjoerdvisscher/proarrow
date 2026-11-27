# Law gallery

Draws every law proarrow states as code as a string-diagram equation, using
`Proarrow.Tools.Diagrams.Svg.lawSvgsWith`, and puts the drawings on one page.

```
python3 proarrow/tools/law-gallery/gallery.py wiki ../proarrow.wiki
python3 proarrow/tools/law-gallery/gallery.py html law-diagrams.html
python3 proarrow/tools/law-gallery/gallery.py zx zx-rules.html
```

`wiki` writes `Law-diagrams.md` and `images/law-diagrams/*.svg` into a clone of the GitHub wiki,
with the SVGs coloured for GitHub's light and dark themes. `html` writes a standalone page from
`template.html`.

For the law gallery the script runs `cabal repl lib:proarrow` from the repository root, so it needs a
working build. `SECTIONS` in `gallery.py` lists what is drawn: for each section, the structure
lists whose laws it shows, the `Options` each is drawn with, and the text introducing it.

`zx` uses `cabal repl test:test` and the same SVG equation layout. It draws the fixed ZX cleanup
rules with symbolic phase and leg labels, plus colour change on a three-legged spider.
