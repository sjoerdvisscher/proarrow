#!/usr/bin/env python3
"""Render the tested optic-composition example: render.py OUTPUT_DIRECTORY."""

from pathlib import Path
from shutil import copyfile
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'law-gallery'))
from gallery import hs_string, run_repl, standalone  # noqa: E402


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    destination = Path(sys.argv[1]).resolve()
    destination.mkdir(parents=True, exist_ok=True)
    pictures = [
        ('source', 'sourcePicture', False),
        ('encoded', 'encodedPicture', True),
        ('composition', 'compositionPicture', True),
        ('derivative-source', 'derivativeSourcePicture', False),
        ('derivative', 'derivativePicture', True),
    ]
    script = [':m + *Examples.OpticDiagrams']
    for name, function, checked in pictures:
        writer = f'writeFile {hs_string(str(destination / (name + ".svg")))}'
        expression = f'Examples.OpticDiagrams.{function}'
        script.append(f'either fail ({writer}) {expression}' if checked else f'{writer} {expression}')
    run_repl('test:test', script)
    for name, _, _ in pictures:
        path = destination / (name + '.svg')
        path.write_text(standalone(path.read_text(encoding='utf-8')), encoding='utf-8')
    copyfile(Path(__file__).with_name('template.html'), destination / 'index.html')
    print(f'Written to {destination / "index.html"}')


if __name__ == '__main__':
    main()
