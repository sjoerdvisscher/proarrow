#!/usr/bin/env python3
"""Render the digital-circuit and parallel-build wiki illustrations.

    python3 proarrow/tools/worked-examples/render.py PATH/TO/proarrow.wiki

Run from any directory. Requires ghc, haddock, and tar on PATH for the measured build.
The timeline is a fresh measurement, so its durations depend on the host and its load.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'law-gallery'))

from gallery import render_pictures  # noqa: E402


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    render_pictures(sys.argv[1], 'circuit', [
        ':m + *Examples.Circuit',
        'writeFile ({tmp} ++ "counter.svg") counterPicture',
        'either fail (writeFile ({tmp} ++ "gates.svg")) simplifiedCounterPicture',
        'either (\\err -> fail (show err)) (writeFile ({tmp} ++ "waveform.svg")) waveform',
    ])
    render_pictures(sys.argv[1], 'parallel', [
        ':m + *Examples.Parallel',
        'demo {tmp}',
    ])


if __name__ == '__main__':
    main()
