import re
import unittest

from tests.utils import PROJECT_ROOT

# `scripts/publish-public.sh` leaves out the private files (dev/, CLAUDE.md, .claude): a link to
# them from a published Markdown file is dead in the public repository (README.md linked
# dev/deep-logic-experiments.md until 2026-10-11)

PRIVATE = ('dev/', 'CLAUDE.md', '.claude/')
LINK = re.compile(r'\]\(([^)#\s]+)')


def published_markdown():
    for path in sorted(PROJECT_ROOT.rglob('*.md')):
        relative = path.relative_to(PROJECT_ROOT).as_posix()
        if relative.startswith(PRIVATE) or relative == 'CLAUDE.md' or '/.' in '/' + relative \
                or relative.startswith(('node_modules/', 'dist/', 'build/')):
            continue
        yield path, relative


class TestPublicLinks(unittest.TestCase):
    def test_published_files_link_nothing_private(self):
        for path, relative in published_markdown():
            for target in LINK.findall(path.read_text(encoding='utf-8')):
                if '://' in target or target.startswith('mailto:'):
                    continue
                resolved = (path.parent / target).resolve()
                try:
                    inside = resolved.relative_to(PROJECT_ROOT).as_posix()
                except ValueError:
                    continue
                with self.subTest(file=relative, link=target):
                    self.assertFalse(inside.startswith(PRIVATE) or inside == 'CLAUDE.md',
                                     f'{relative} links {target}, which is not published')


if __name__ == '__main__':
    unittest.main()
