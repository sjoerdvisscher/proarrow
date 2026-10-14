"""Regression checks for interface collection in checkout and unpacked CI layouts."""

import json
from pathlib import Path
import tempfile
import unittest

from interfaces import check_index, collect


class InterfacesTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name)
        (self.project / 'cabal.project').write_text('packages: unpacked/proarrow-0.3.0.0\n')

    def prepare(self, location, builddir='dist-newstyle'):
        package = self.project / location
        (package / 'docs').mkdir(parents=True)
        entries = []
        for component, subdir, relative, contents in (
            ('lib', '', 'doc/html/proarrow/proarrow.haddock', b'main interface'),
            ('lib:testing', 'l/testing', 'doc/html/proarrow/testing/testing.haddock', b'testing interface'),
        ):
            dist = self.project / builddir / 'build/platform/compiler/proarrow-0.3.0.0' / subdir
            interface = dist / relative
            interface.parent.mkdir(parents=True)
            interface.write_bytes(contents)
            entries.append({'pkg-name': 'proarrow', 'component-name': component,
                            'pkg-src': {'path': str(package)}, 'dist-dir': str(dist)})
        cache = self.project / builddir / 'cache'
        cache.mkdir()
        (cache / 'plan.json').write_text(json.dumps({'install-plan': entries}))
        return package

    def assert_interfaces(self, package):
        self.assertEqual((package / 'docs/proarrow.haddock').read_bytes(), b'main interface')
        self.assertEqual((package / 'docs/testing.haddock').read_bytes(), b'testing interface')

    def test_checkout(self):
        package = self.prepare('proarrow')
        collect(package, Path('dist-newstyle'))
        self.assert_interfaces(package)

    def test_unpacked_ci(self):
        package = self.prepare('unpacked/proarrow-0.3.0.0')
        self.assertFalse((package.parent / 'dist-newstyle').exists())
        collect(package, Path('dist-newstyle'))
        self.assert_interfaces(package)

    def test_custom_builddir_ignores_stale_interfaces(self):
        package = self.prepare('proarrow', 'dist-9103')
        stale = self.project / 'dist-newstyle/build/old'
        stale.mkdir(parents=True)
        (stale / 'proarrow.haddock').write_bytes(b'stale interface from another compiler')
        collect(package, Path('dist-9103'))
        self.assert_interfaces(package)

    def test_missing_interface_fails(self):
        package = self.prepare('unpacked/proarrow-0.3.0.0')
        next((self.project / 'dist-newstyle/build').rglob('testing.haddock')).unlink()
        with self.assertRaises(FileNotFoundError):
            collect(package, Path('dist-newstyle'))

    def test_combined_index(self):
        index = self.project / 'index.html'
        index.write_text('<p class="caption">proarrow-0.3.0.0</p>'
                         '<p class="caption">proarrow:testing-0.3.0.0</p>')
        check_index(index)

    def test_testing_only_index_fails_even_with_main_library_links(self):
        index = self.project / 'index.html'
        index.write_text('<p class="caption">proarrow:testing-0.3.0.0</p>'
                         '<a href="Proarrow.html">Start here</a>'
                         '<a href="Proarrow-Core.html">Core</a>')
        with self.assertRaises(ValueError):
            check_index(index)


if __name__ == '__main__':
    unittest.main()
