import importlib.util
import re
import sys
import tempfile
import unittest
from pathlib import Path

from tests.utils import PROJECT_ROOT

# scripts/build_reference_site.py: doc/kurt-ref.md as a website (MkDocs, Material). The splitting and
# the rewriting of the links need only the standard library; the real `mkdocs build` runs only where
# mkdocs-material is installed.

sys.path.insert(0, str(PROJECT_ROOT / 'scripts'))
import build_reference_site as site  # noqa: E402
sys.path.remove(str(PROJECT_ROOT / 'scripts'))   # (only needed for the import above)

DOC = (PROJECT_ROOT / 'doc/kurt-ref.md').read_text(encoding='utf-8')
LINK = re.compile(r'\]\(([^)\s]+)\)')


def installed(*modules):
    return all(importlib.util.find_spec(m) is not None for m in modules)


class TestSplit(unittest.TestCase):
    def setUp(self):
        self.pages = site.split_reference(DOC)

    def test_every_line_exactly_once(self):
        # the pages, one after the other, are the doc: nothing lost, nothing doubled, nothing reordered
        self.assertEqual([line for page in self.pages for line in page.lines], DOC.split('\n'))

    def test_one_page_per_top_level_section(self):
        code = site.code_block_lines(DOC.split('\n'))
        sections = [m.group(1) for i, line in enumerate(DOC.split('\n'))
                    if i not in code and (m := site.TOP.match(line))]
        self.assertGreater(len(sections), 10)
        self.assertEqual([p.number for p in self.pages], [None] + sections)
        self.assertEqual(self.pages[0].file, 'index.md')
        files = [p.file for p in self.pages]
        self.assertEqual(len(files), len(set(files)))
        for page in self.pages[1:]:
            self.assertTrue(page.lines[0].startswith(f'## {page.number}. '))

    def test_every_numbered_heading_has_one_anchor(self):
        numbers = re.findall(r'^#{2,4} (\d+(?:\.\d+)*)\.? ', DOC, re.M)
        anchors = [a for page in self.pages for a in page.anchors]
        self.assertEqual(sorted(anchors), sorted(site.anchor(n) for n in numbers))
        self.assertEqual(len(anchors), len(set(anchors)))
        self.assertIn('sec-6-3-1', anchors)

    def test_page_names_come_from_titles(self):
        self.assertEqual(site.page_slug('8', 'Building the theory: hard-coded core vs. loaded theories'),
                         'building-the-theory')
        self.assertEqual(site.page_slug('7', 'Goal-directed proof: `show` / `proof` / `qed`'), 'goal-directed-proof')
        self.assertEqual(site.page_slug('11', "Known gaps (so you don't mistake them)"), 'known-gaps')
        self.assertEqual(site.page_slug('4', '`bindop`'), 'section-4')


class TestPages(unittest.TestCase):
    def setUp(self):
        self.pages = site.split_reference(DOC)
        self.markdown = site.build_pages(DOC)
        self.anchors = {p.file: p.anchors for p in self.pages}

    def test_pages(self):
        self.assertEqual(list(self.markdown), [p.file for p in self.pages])
        for name, md in self.markdown.items():
            with self.subTest(page=name):
                self.assertEqual(len(re.findall(r'^# ', md, re.M)), 1, 'one title per page')

    def test_every_internal_link_resolves(self):
        count = 0
        for name, md in self.markdown.items():
            for target in LINK.findall(md):
                if '://' in target:
                    continue
                count += 1
                file, _, anchor = target.partition('#')
                file = file or name
                with self.subTest(page=name, link=target):
                    self.assertIn(file, self.markdown)
                    if anchor:
                        self.assertIn(anchor, self.anchors[file])
        self.assertGreater(count, 50)

    def test_every_reference_to_a_section_is_a_link(self):
        for name, md in self.markdown.items():
            prose = re.sub(r'```.*?```', '', md, flags=re.S)
            prose = re.sub(r'\[§[\d.]+\]\([^)]*\)', '', prose)
            for m in re.finditer(r'§(\d+(?:\.\d+)*)', prose):
                before = prose[max(0, m.start() - 300):m.start()]
                with self.subTest(page=name, ref=m.group(0), context=before[-60:]):
                    # what is left is a section of another document (`doc/kurt-kernel.md §8`)
                    self.assertRegex(before, r'\.md(\)|`)?(?:\s|,|-|–|§\d+(?:\.\d+)*)*$')

    def test_references_to_other_documents_stay_text(self):
        line = 'the argument (doc/kurt-kernel.md §8) and §8.2'
        index = site.section_index(self.pages)
        out = site.rewrite_line(line, '', index, 'index.md', PROJECT_ROOT)
        self.assertIn('[doc/kurt-kernel.md](https://github.com/harmeling/kurt-lang/blob/main/doc/kurt-kernel.md) §8)', out)
        self.assertIn('[§8.2](building-the-theory.md#sec-8-2)', out)
        # on its own page, an anchor alone; the top of a page, the page alone
        self.assertEqual(site.rewrite_line('§8.2', '', index, 'building-the-theory.md', PROJECT_ROOT),
                         '[§8.2](#sec-8-2)')
        self.assertEqual(site.rewrite_line('(§5)', '', index, 'index.md', PROJECT_ROOT),
                         '([§5](statements-terms-and-sorts.md))')

    def test_github_links_only_to_public_files(self):
        for name, md in self.markdown.items():
            for target in LINK.findall(md):
                if target.startswith(site.GITHUB):
                    path = re.sub(r'^(blob|tree)/main/', '', target[len(site.GITHUB):])
                    with self.subTest(page=name, link=target):
                        self.assertTrue((PROJECT_ROOT / path).exists())
                        self.assertFalse(path.startswith(site.PRIVATE))
        out = site.rewrite_line('see `dev/todo.md` and `path/to/proof.kurt`', '', {}, 'index.md', PROJECT_ROOT)
        self.assertEqual(out, 'see `dev/todo.md` and `path/to/proof.kurt`')

    def test_code_blocks_fenced(self):
        code = site.code_block_lines(DOC.split('\n'))
        blocks = sum(1 for i in code if i - 1 not in code)
        fences = sum(len(re.findall(r'^```(kurt|text)$', md, re.M)) for md in self.markdown.values())
        self.assertEqual(fences, blocks)
        self.assertEqual(site.block_language(['kurt -i path/to/proof.kurt']), 'text')
        self.assertEqual(site.block_language(['TypeError: `x` has the sort']), 'text')
        self.assertEqual(site.block_language(['load propositional', 'show A']), 'kurt')

    @unittest.skipUnless(installed('pygments'), 'Pygments is not installed')
    def test_kurt_lexer(self):
        token = importlib.import_module('pygments.token')     # (not imported by name: see make_kurt_lexer)
        Comment, Keyword, Name, String = token.Comment, token.Keyword, token.Name, token.String
        lexer = site.make_kurt_lexer(site.kurt_keywords(PROJECT_ROOT))()
        tokens = [(t, v) for t, v in lexer.get_tokens('use $a = $b "eq" ; a rule\nshow A implies A\n') if v.strip()]
        self.assertIn((Keyword, 'use'), tokens)
        self.assertIn((Keyword, 'show'), tokens)
        self.assertIn((Name.Variable, '$a'), tokens)
        self.assertIn((String, '"eq"'), tokens)
        self.assertIn((Comment.Single, '; a rule'), tokens)


@unittest.skipUnless(installed('mkdocs', 'material'), 'mkdocs-material is not installed')
class TestBuild(unittest.TestCase):
    def test_mkdocs_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / 'site'
            self.assertEqual(site.main(['--out', str(out), '--strict']), 0)
            self.assertTrue((out / 'index.html').exists())
            html = (out / 'building-the-grammar/index.html').read_text(encoding='utf-8')
            self.assertIn('id="sec-4-6"', html)
            self.assertIn('<span class="kd">chain</span>', html)       # highlighted as Kurt
            self.assertIn('href="../terms-symbols-and-their-roles/#sec-3-1"', html)
            self.assertTrue((out / 'search/search_index.json').exists())


if __name__ == '__main__':
    unittest.main()
