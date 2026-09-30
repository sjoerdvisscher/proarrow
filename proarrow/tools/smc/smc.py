#!/usr/bin/env python3
"""Draw the pictures of the wiki's Linear-terms-for-monoidal-categories page.

    python3 proarrow/tools/smc/smc.py PATH/TO/proarrow.wiki

The pictures are Examples.Toffoli.toffoliPicture, Examples.IntComposition.compositionPicture and
Examples.LinearLogic.snakePicture,
rendered through `cabal repl test:test` run from the repository root, and coloured for GitHub's
light and dark themes the same way as the law diagrams.
"""

import os
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'law-gallery'))

from gallery import hs_string, read, run_repl, standalone, write  # noqa: E402

PICTURES = [
    ('Examples.Toffoli', 'toffoliPicture', 'toffoli-circuit.svg'),
    ('Examples.IntComposition', 'compositionPicture', 'int-composition.svg'),
    ('Examples.LinearLogic', 'snakePicture', 'snake.svg'),
]


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    target_dir = os.path.join(sys.argv[1], 'images', 'smc')
    os.makedirs(target_dir, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        script = [':m + ' + ' '.join('*' + module for module, _, _ in PICTURES)]
        for module, name, file in PICTURES:
            script.append(f'writeFile {hs_string(os.path.join(tmp, file))} {module}.{name}')
        run_repl('test:test', script)
        for _, _, file in PICTURES:
            target = os.path.join(target_dir, file)
            write(target, standalone(read(os.path.join(tmp, file))))
            print(f'written to {target}')


if __name__ == '__main__':
    main()
