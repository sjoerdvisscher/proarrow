#!/usr/bin/env python3
"""Draw the Toffoli circuit of test/Examples/Toffoli.hs for the wiki's Toffoli-gate page.

    python3 proarrow/tools/toffoli/toffoli.py PATH/TO/proarrow.wiki

The picture is Examples.Toffoli.toffoliPicture, rendered through `cabal repl test:test` run from the
repository root, and coloured for GitHub's light and dark themes the same way as the law diagrams.
"""

import os
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'law-gallery'))

from gallery import hs_string, read, run_repl, standalone, write  # noqa: E402


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    target = os.path.join(sys.argv[1], 'images', 'toffoli', 'toffoli-circuit.svg')
    with tempfile.TemporaryDirectory() as tmp:
        raw = os.path.join(tmp, 'toffoli-circuit.svg')
        run_repl('test:test', [':m + *Examples.Toffoli', f'writeFile {hs_string(raw)} toffoliPicture'])
        svg = read(raw)
    os.makedirs(os.path.dirname(target), exist_ok=True)
    write(target, standalone(svg))
    print(f'written to {target}')


if __name__ == '__main__':
    main()
