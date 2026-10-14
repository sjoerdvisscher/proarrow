#!/usr/bin/env python3
"""Draw the pictures of the wiki's Programming-with-monoidal-categories page.

    python3 proarrow/tools/smc/smc.py PATH/TO/proarrow.wiki

The pictures are the Toffoli circuit, the Yampa feedback echo, composition in the Int construction
and the snake equation, rendered through `cabal repl test:test` run from the repository root,
and coloured for GitHub's light and dark themes the same way as the law diagrams.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'law-gallery'))

from gallery import hs_string, render_pictures  # noqa: E402

PICTURES = [
    ('Examples.Toffoli', 'toffoliPicture', 'toffoli-circuit.svg'),
    ('SmcAudio', 'echoPicture', 'feedback-echo.svg'),
    ('Examples.IntComposition', 'compositionPicture', 'int-composition.svg'),
    ('Examples.LinearLogic', 'snakePicture', 'snake.svg'),
]


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    script = [':m + ' + ' '.join('*' + module for module, _, _ in PICTURES)]
    for module, name, file in PICTURES:
        script.append(f'writeFile ({{tmp}} ++ {hs_string(file)}) {module}.{name}')
    render_pictures(sys.argv[1], 'smc', script)


if __name__ == '__main__':
    main()
