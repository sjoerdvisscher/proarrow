#!/usr/bin/env python3
"""Draw every law proarrow states as code, as string diagrams, into an HTML page or the wiki.

    python3 proarrow/tools/law-gallery/gallery.py html OUT.html
    python3 proarrow/tools/law-gallery/gallery.py wiki PATH/TO/proarrow.wiki

The diagrams are rendered by Proarrow.Tools.Diagrams.Svg.lawSvgsWith, through `cabal repl
lib:proarrow` run from the repository root. SECTIONS below is the one place that says which laws
are drawn, with which options, and how each section is introduced.
"""

import html
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))

# Each section draws the laws of one or more structure lists, each with its options: the fields of
# Options to switch from defaultOptions, or '' for defaultOptions itself.
SECTIONS = [
    dict(key='category', title='Category', parts=[("'[CategoryOf]", 'explicitIdentities = True')],
         desc='Identities are units for composition, which is associative. Drawn with explicit identities, so each id is a dashed frame; associativity draws the same on both sides, as a string diagram does not record how a composite was bracketed.'),
    dict(key='monoidal', title='Monoidal', parts=[("'[Monoidal]", 'explicitCoherence = True')],
         desc='Unitors and associator are invertible and natural, the tensor is a bifunctor, and the triangle and pentagon commute. Drawn with explicit coherence. The unit is a wire of its own, drawn dotted and labelled 𝐈, so a unitor is a unit wire running into another wire or out of it. The associator is drawn with brackets: at the top the pair grouped in its input, at the bottom the pair grouped in its output. Without explicit coherence, both sides of these laws draw the same. Tensor interchange draws the same either way: that string diagrams do not tell the two apart is what the law says.'),
    dict(key='symmetric', title='Symmetric monoidal', parts=[('SymMonoidalStructures', 'explicitSwaps = True')],
         desc='The swap undoes itself, is natural, and satisfies the hexagon. Drawn with explicit swaps, so each swap is a crossing of its own; without them, a swap only moves wires and most of these draw the same.'),
    dict(key='traced', title='Traced', parts=[('TracedStructures', 'explicitCoherence = True')],
         desc='The trace of f over u feeds its u output back to its u input, drawn as a loop round the side. It is natural in the other wires, slides along the loop, is trivial over the unit and nests over a tensor, lets a wire run past, and turns a swap into a plain wire. Drawn with explicit coherence, so the trace over the unit is a dotted loop and the regroupings the nested traces need show as brackets.'),
    dict(key='starautonomous', title='*-autonomous', parts=[('StarAutonomousStructures', 'fixedSpiders = False')],
         desc='Duals and linear distribution. The dual of a wire is a wire of its own, labelled with ⁻¹ and drawn hollow. A wire is bent with a cup or a cap, drawn as one bend: the half that runs backwards is the dual wire, and the style switches at the apex. Double negation is only a relabelling here, so its inverse laws are straight wires; the definition law compares it with the one derived from linDist and the duality unit. Drawn with free spider legs.'),
    dict(key='closed', title='Closed', parts=[('ClosedStructures', 'fixedSpiders = False')],
         desc='Currying and apply. The exponential is the *-autonomous one, the dual of a ⊗ b⁻¹, so curry bends a wire round, and the part running backwards is a dual wire. Drawn with free spider legs, so the legs of a point trade places to avoid crossings.'),
    dict(key='compactclosed', title='Compact closed', parts=[('CompactClosedStructures', 'fixedSpiders = False')],
         desc='The zigzag identities, with the duality unit and counit drawn as one bend each, so a zigzag is a wire bent up and down again, dual on its middle stretch. The definition laws compare them with the ones derived from the *-autonomous structure.'),
    dict(key='monoids', title='Monoids',
         parts=[("'[Monoidal, Supplies Monoid]", 'explicitCoherence = True'),
                ("'[Monoidal, SymMonoidal, Supplies CommutativeMonoid]", '')],
         desc='Every object is a monoid: the unit point is a unit for the merge point, which is associative, and commutative when the monoids are commutative ones. The unit laws are drawn with explicit coherence, so they show the unitor they equal.'),
    dict(key='comonoids', title='Comonoids',
         parts=[("'[Monoidal, Supplies Comonoid]", 'explicitCoherence = True'),
                ("'[Monoidal, SymMonoidal, Supplies CocommutativeComonoid]", '')],
         desc='Every object is a comonoid: the discard point is a counit for the copy point, which is coassociative, and cocommutative when the comonoids are cocommutative ones. The counit laws are drawn with explicit coherence.'),
    dict(key='copydiscard', title='Copy and discard', parts=[('CopyDiscardStructures', 'explicitCoherence = True')],
         desc='A copy-discard category copies and discards with its supplied comonoids, and these respect the tensor: copying or discarding a pair is copying or discarding both parts, and on the unit they do nothing. Drawn with explicit coherence, so the unit wire and the regrouping show.'),
    dict(key='frobenius', title='Frobenius', parts=[('FrobeniusStructures', '')],
         desc='The monoids and comonoids together are special Frobenius algebras: a copy then a merge is the identity, and the Frobenius law holds. These are the spiders that make every other bend here work.'),
]

GHCI_HEADER = '''\
:set -XNoOverloadedLists -XDataKinds -XTypeApplications
import Prelude hiding (Monoid)
import Proarrow.Tools.Diagrams.Svg
import Proarrow.Core (CategoryOf)
import Proarrow.Category.Monoidal
import Proarrow.Monoid (Supplies, Monoid, Comonoid, CommutativeMonoid, CocommutativeComonoid)
import Proarrow.Category.Monoidal.Hypergraph (FrobeniusStructures)
import Proarrow.Category.Monoidal.Strength (TracedStructures)
import Proarrow.Category.Monoidal.CopyDiscard (CopyDiscardStructures)
import Proarrow.Category.Monoidal.Closed (ClosedStructures)
import Proarrow.Category.Monoidal.StarAutonomous (StarAutonomousStructures)
import Proarrow.Category.Monoidal.CompactClosed (CompactClosedStructures)
'''


def call(structures, opts):
    """The Haskell expression drawing the laws of one structure list."""
    if opts:
        return f'lawSvgsWith @{structures} defaultOptions{{{opts}}}'
    return f'lawSvgs @{structures}'


def draw(out):
    """Render every section's diagrams into the directory out, as <key>-<n>.svg. Returns the rows
    (file id, section key, law name), in order."""
    script = [GHCI_HEADER]
    script.append(f'let out = {hs_string(out)}')
    script.append('let save grp ds = mapM_ (\\(i, (n, d)) -> writeFile (out ++ "/" ++ grp ++ "-" ++ show i ++ ".svg") d'
                  ' >> appendFile (out ++ "/index.txt") (grp ++ "-" ++ show i ++ "\\t" ++ grp ++ "\\t" ++ n ++ "\\n"))'
                  ' (zip [1 :: Int ..] ds)')
    script.append('writeFile (out ++ "/index.txt") ""')
    for s in SECTIONS:
        script.append(f'save {hs_string(s["key"])} (' + ' ++ '.join(call(*p) for p in s['parts']) + ')')
    result = subprocess.run(['cabal', 'repl', '-v0', 'lib:proarrow'], cwd=ROOT, input='\n'.join(script) + '\n',
                            capture_output=True, text=True)
    if result.returncode != 0 or re.search(r'error|exception', result.stdout + result.stderr, re.I):
        sys.exit(result.stdout + result.stderr)
    with open(os.path.join(out, 'index.txt'), encoding='utf-8') as f:
        rows = [line.rstrip('\n').split('\t') for line in f if line.strip()]
    if not rows:
        sys.exit('no diagrams were drawn:\n' + result.stdout + result.stderr)
    return rows


def hs_string(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read()


def write(path, text):
    with open(path, 'w', encoding='utf-8') as f:
        f.write(text)


def html_page(svgs, rows, target):
    template = read(os.path.join(HERE, 'template.html'))
    out = ['<nav aria-label="Structures">']
    for s in SECTIONS:
        count = sum(1 for r in rows if r[1] == s['key'])
        out.append(f'<a href="#{s["key"]}">{s["title"]}<span>{count}</span></a>')
    out.append('</nav>')
    for s in SECTIONS:
        codes = ''.join(f'<p><code>{html.escape(call(*p))}</code></p>' for p in s['parts'])
        out.append(f'<section id="{s["key"]}"><div class="sh"><h2>{s["title"]}</h2><p>{html.escape(s["desc"])}</p>'
                   f'{codes}</div><div class="grid">')
        for fid, key, name in rows:
            if key != s['key']:
                continue
            svg = read(os.path.join(svgs, fid + '.svg'))
            svg = svg.replace('<svg ', '<svg role="img" aria-label="' + html.escape(name) + '" ', 1)
            w = float(re.search(r'viewBox="[-\d.]+ [-\d.]+ ([\d.]+)', svg).group(1))
            cls = ' class="wide"' if w > 520 else ''
            out.append(f'<figure{cls}><figcaption>{html.escape(name)}</figcaption><div class="dia">{svg}</div></figure>')
        out.append('</div></section>')
    out.append('<footer>Generated by <code>Proarrow.Tools.Diagrams.Svg.lawSvgs</code>, which lays each diagram out'
               ' from how it is built: tensors side by side, composites stacked with a band of wires between them,'
               ' and trace loops round the side.</footer>')
    write(target, template.replace('<!-- sections -->', '\n'.join(out)))
    print(f'{len(rows)} diagrams written to {target}')


WIKI_INTRO = '''\
The laws proarrow states as code, drawn as string diagrams. Each law is an equation between two ways of building an arrow, and each picture draws both sides exactly as the law builds them, without simplifying either one. So where a law says two different constructions agree, you see two different pictures next to each other.

The object variables of a law are single wires, labelled *a* to *e*, and the arbitrary arrows a law asks for are boxes with the names the law gives them. Copying and merging are drawn as points, a dual wire is drawn hollow and labelled with ⁻¹, the unit is a dotted wire labelled **I**, and a trace is a loop round the side.

The pictures are made by `Proarrow.Tools.Diagrams.Svg`, which lays each diagram out from how it is built: a tensor puts its sides next to each other, a composite stacks them with a band of wires in between, and a trace draws its loops. Some sections are drawn with options that show more of the structure; the code under each heading says which.

'''


def standalone(svg):
    """An SVG for a page that does not style it: GitHub's own colours, light and dark, chosen by the
    reader's colour scheme. Only the core of a dual wire is painted; it gets GitHub's default dark
    background, written out rather than left to a CSS variable, which not every SVG renderer
    supports."""
    svg = svg.replace('var(--sd-paper,#fff)', '#ffffff')
    theme = '.sd{color:#1f2328}@media (prefers-color-scheme: dark){.sd{color:#e6edf3}.sd .di path{stroke:#0d1117}}'
    return svg.replace('</style>', theme + '</style>', 1)


def wiki_page(svgs, rows, wiki):
    img = os.path.join(wiki, 'images', 'law-diagrams')
    os.makedirs(img, exist_ok=True)
    for fid, _, _ in rows:
        write(os.path.join(img, fid + '.svg'), standalone(read(os.path.join(svgs, fid + '.svg'))))
    anchor = lambda title: title.lower().replace(' ', '-').replace('*', '')
    out = [WIKI_INTRO, ' · '.join(f'[{s["title"]}](#{anchor(s["title"])})' for s in SECTIONS) + '\n']
    for s in SECTIONS:
        codes = '  \n'.join(f'`{call(*p)}`' for p in s['parts'])
        out.append(f'\n## {s["title"]}\n\n{s["desc"]}\n\n{codes}\n')
        cells = []
        for fid, key, name in rows:
            if key != s['key']:
                continue
            w = float(re.search(r'width="([\d.]+)"', read(os.path.join(svgs, fid + '.svg'))).group(1))
            cells.append(f'<td align="center" valign="top"><b>{html.escape(name)}</b><br>'
                         f'<img src="images/law-diagrams/{fid}.svg" alt="{html.escape(name)}" width="{min(300, round(w))}"></td>')
        out.append('\n<table>\n' + ''.join('<tr>' + ''.join(cells[i:i + 3]) + '</tr>\n' for i in range(0, len(cells), 3))
                   + '</table>\n')
    write(os.path.join(wiki, 'Law-diagrams.md'), ''.join(out))
    print(f'{len(rows)} diagrams written to {wiki}')


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in ('html', 'wiki'):
        sys.exit(__doc__)
    mode, target = sys.argv[1], os.path.abspath(sys.argv[2])
    with tempfile.TemporaryDirectory() as svgs:
        rows = draw(svgs)
        if mode == 'html':
            html_page(svgs, rows, target)
        else:
            wiki_page(svgs, rows, target)


if __name__ == '__main__':
    main()
