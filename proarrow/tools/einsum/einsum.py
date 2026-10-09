#!/usr/bin/env python3
"""Draw the pictures of the wiki's einsum page.

    python3 proarrow/tools/einsum/einsum.py PATH/TO/proarrow.wiki

The pictures are Examples.Einsum.gallery and Examples.Einsum.ringPictures, rendered through
`cabal repl test:test` run from the repository root, and coloured for GitHub's light and dark
themes the same way as the law diagrams.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'law-gallery'))

from gallery import render_pictures  # noqa: E402


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    render_pictures(sys.argv[1], 'einsum', [
        ':m + *Examples.Einsum',
        'mapM_ (\\(f, s) -> writeFile ({tmp} ++ f) s) (gallery ++ ringPictures)',
    ])


if __name__ == '__main__':
    main()
