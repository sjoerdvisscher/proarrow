#!/usr/bin/env python3
"""Collect library interfaces and check the combined Haddock index."""

import argparse
import json
from html.parser import HTMLParser
from pathlib import Path
import shutil
import sys


def collect(package, builddir):
    package = package.resolve()
    project = next((p for p in (package, *package.parents) if (p / 'cabal.project').is_file()), None)
    if project is None:
        raise ValueError('No cabal.project found above the package directory')
    plan = json.loads((project / builddir / 'cache/plan.json').read_text())
    for component, relative in (
        ('lib', 'doc/html/proarrow/proarrow.haddock'),
        ('lib:testing', 'doc/html/proarrow/testing/testing.haddock'),
    ):
        entries = [entry for entry in plan['install-plan']
                   if entry.get('pkg-name') == 'proarrow'
                   and entry.get('component-name') == component
                   and Path(entry.get('pkg-src', {}).get('path', '')).resolve() == package]
        if len(entries) != 1:
            raise ValueError(f'Expected one local proarrow {component} in the build plan, found {len(entries)}')
        source = Path(entries[0]['dist-dir']) / relative
        shutil.copyfile(source, package / 'docs' / source.name)


def check_index(index):
    class Captions(HTMLParser):
        def __init__(self):
            super().__init__()
            self.current = None
            self.packages = set()

        def handle_starttag(self, tag, attrs):
            if tag == 'p' and 'caption' in dict(attrs).get('class', '').split():
                self.current = []

        def handle_data(self, data):
            if self.current is not None:
                self.current.append(data)

        def handle_endtag(self, tag):
            if tag == 'p' and self.current is not None:
                self.packages.add(''.join(self.current).strip().rsplit('-', 1)[0])
                self.current = None

    captions = Captions()
    captions.feed(index.read_text())
    missing = {'proarrow', 'proarrow:testing'} - captions.packages
    if missing:
        raise ValueError(f'{index} does not list packages: {", ".join(sorted(missing))}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-index', action='store_true')
    parser.add_argument('--builddir', type=Path, default=Path('dist-newstyle'))
    args, _ = parser.parse_known_args()
    try:
        if args.check_index:
            check_index(Path('docs/index.html'))
        else:
            collect(Path.cwd().resolve(), args.builddir)
    except (OSError, ValueError, KeyError) as error:
        sys.exit(f'Haddock documentation: {error}')


if __name__ == '__main__':
    main()
