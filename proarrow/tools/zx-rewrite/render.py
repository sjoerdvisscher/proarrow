#!/usr/bin/env python3
"""Render the ZX rewriting example's before and after diagrams.

    python3 proarrow/tools/zx-rewrite/render.py OUTPUT_DIRECTORY

Requires Graphviz's dot on PATH and a working Cabal build.
"""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    root = Path(__file__).resolve().parents[3]
    with tempfile.TemporaryDirectory(prefix='proarrow-zx-') as temporary:
        directory = json.dumps(temporary + '/')
        script = '\n'.join([
            ':m + Examples.ZXRewrite',
            f'either fail (mapM_ (\\(name, contents) -> writeFile ({directory} ++ name) contents)) pictures',
            ':quit',
            '',
        ])
        result = subprocess.run(
            ['cabal', 'repl', '-v0', 'test:test'], cwd=root,
            input=script, text=True, capture_output=True,
        )
        sources = sorted(Path(temporary).glob('*.dot'))
        expected = ['before', 'after', 'local-before', 'local-after']
        if result.returncode or any(not (Path(temporary) / f'{name}.dot').exists() for name in expected):
            raise SystemExit(result.stdout + result.stderr)
        for source in sources:
            target = args.output / f'{source.stem}.svg'
            subprocess.run(['dot', '-Tsvg', str(source), '-o', str(target)], check=True)
            print(target)


if __name__ == '__main__':
    main()
