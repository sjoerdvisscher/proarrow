#!/usr/bin/env python3
# Point every per-entity "Github" link in the generated docs at the same place as the "Source"
# link next to it.
#
# Haddock fills the --comments-entity template with the module of the page being rendered and the
# line of the enclosing declaration, so it goes wrong for instances and re-exports listed under
# another module, and for class members (which get the line of their class). The hyperlinked
# source is right, so this derives the Github URL from it: the defining module picks the file
# (under src/ or testing/), and the entity's position in docs/src/<module>.html gives the line.
#
# Usage (from proarrow/, after haddock has written docs/): fix-github-links.py DOCS GITHUB_BASE
# where GITHUB_BASE is e.g. https://github.com/sjoerdvisscher/proarrow/blob/main/proarrow/

import glob
import os
import re
import sys

docs, base = sys.argv[1], sys.argv[2]
source_dirs = ["src", "testing"]

# The anchor ids in docs/src/<module>.html and the line each one is on.
lines = {}


def anchor_line(module, anchor):
    if anchor.startswith("line-"):
        return int(anchor[len("line-") :])
    if module not in lines:
        table, current = {}, 0
        with open(os.path.join(docs, "src", module + ".html"), encoding="utf-8") as f:
            for m in re.finditer(r'id="([^"]+)"', f.read()):
                if m.group(1).startswith("line-"):
                    current = int(m.group(1)[len("line-") :])
                else:
                    table.setdefault(m.group(1), current)
        lines[module] = table
    return lines[module].get(anchor)


def source_file(module):
    path = module.replace(".", "/") + ".hs"
    for d in source_dirs:
        if os.path.exists(os.path.join(d, path)):
            return d + "/" + path
    return None


pair = re.compile(
    r'(<a href="src/([^"#]+)\.html#([^"]+)" class="link"\s*>Source</a\s*>\s*<a href=")'
    + re.escape(base)
    + r'[^"]*(" class="link")'
)

changed = unresolved = 0
for page in glob.glob(os.path.join(docs, "*.html")):
    with open(page, encoding="utf-8") as f:
        text = f.read()

    def fix(m):
        global changed, unresolved
        module, anchor = m.group(2), m.group(3)
        line, path = anchor_line(module, anchor), source_file(module)
        if line is None or path is None:
            unresolved += 1
            return m.group(0)
        changed += 1
        return f"{m.group(1)}{base}{path}#L{line}{m.group(4)}"

    new = pair.sub(fix, text)
    if new != text:
        with open(page, "w", encoding="utf-8") as f:
            f.write(new)

print(f"fix-github-links: {changed} links set from their Source link, {unresolved} left as they were")
