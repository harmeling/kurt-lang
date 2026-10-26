#!/usr/bin/env python3
"""The reference doc/kurt-ref.md as a website, with MkDocs (the Material theme).

    python3 scripts/build_reference_site.py                 # the site in site/reference/
    python3 scripts/build_reference_site.py --out DIR       # ... in DIR
    python3 scripts/build_reference_site.py --pages DIR     # only the Markdown pages and mkdocs.yml, no build

doc/kurt-ref.md stays the only source: this script splits it into pages, one per top-level section
(`## N. Title`; the text before the first one is the start page), and turns the references to its
sections (`§4.6`) into links to the right page and anchor (a numbered heading `N.M` gets the anchor
`sec-N-M`), the paths of the repository it mentions (`doc/kurt-spec.md`, `keywords/00-true.kurt`)
into links to the public repository on GitHub, and its indented code blocks into fenced ones,
`kurt` (highlighted by a small Pygments lexer, `KurtLexer`, registered by this file as an MkDocs
hook) or plain text (shell commands, output). Nothing generated is committed; the site is built
where it is published (kurt-web's update.sh, next to the playground).

`mkdocs build` needs `pip install mkdocs-material`; splitting and rewriting (`split_reference`,
`build_pages`) need only the standard library (tests/test_reference_site.py).
"""
from __future__ import annotations

import argparse
import ast
import importlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import unicodedata
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GITHUB = 'https://github.com/harmeling/kurt-lang/'
SITE_URL = 'https://harmeling.github.io/kurt-web/reference/'
PLAYGROUND_URL = 'https://harmeling.github.io/kurt-web/'
PRIVATE = ('dev/', 'CLAUDE.md', '.claude/')       # not in the public repository (scripts/publish-public.sh)

TOP = re.compile(r'^## (\d+)\. (.+?)\s*$')
HEADING = re.compile(r'^(#{2,6}) (.+?)\s*$')
NUMBERED = re.compile(r'^(\d+(?:\.\d+)*)\.? (.+)$')    # `4.6 chain`, `6.3.1 Definitions`, `5. Statements`
SECREF = re.compile(r'§(\d+(?:\.\d+)*)')
CODESPAN = re.compile(r'(`+)(.+?)\1')
PATHLIKE = re.compile(r'(?<![\w/.-])((?:doc|proofs|keywords|tutorial|exercises|src|scripts|tests)/[\w./-]*[\w/])')


@dataclass
class Page:
    file: str                         # e.g. `building-the-grammar.md`
    title: str                        # e.g. `4. Building the grammar`
    number: str | None                # the section's number, None for the start page
    lines: list[str]                  # the source lines of kurt-ref.md, unchanged
    first_line: int                   # its first line in kurt-ref.md (1-based)
    anchors: set[str] = field(default_factory=set)    # the explicit anchors of its numbered headings


def slugify(text: str) -> str:
    text = unicodedata.normalize('NFKD', text).encode('ascii', 'ignore').decode()
    text = re.sub(r'[^\w\s-]', '', text).strip().lower()
    return re.sub(r'[-\s]+', '-', text)


def page_slug(number: str, title: str) -> str:
    """The page of a section: its title up to a colon or parenthesis, without code -- stable while the
    title is, whatever the section's number (`8. Building the theory: ...` -> `building-the-theory`)."""
    short = re.split(r'[:(]', title)[0]
    short = CODESPAN.sub('', short)
    return slugify(short) or f'section-{number}'


def anchor(number: str) -> str:
    return 'sec-' + number.replace('.', '-')


def code_block_lines(lines: list[str]) -> set[int]:
    """The indices of the lines in indented code blocks (after a blank line or a heading, 4 spaces)."""
    inside: set[int] = set()
    i = 0
    while i < len(lines):
        prev_blank = i == 0 or not lines[i - 1].strip() or lines[i - 1].startswith('#')
        if lines[i].startswith('    ') and prev_blank:
            j = i
            while j < len(lines) and (lines[j].startswith('    ')
                                      or (not lines[j].strip() and j + 1 < len(lines) and lines[j + 1].startswith('    '))):
                inside.add(j)
                j += 1
            i = j
        else:
            i += 1
    return inside


def split_reference(text: str) -> list[Page]:
    """kurt-ref.md as pages: the start page (everything before `## 0.`), then one per `## N. Title`."""
    lines = text.split('\n')
    code = code_block_lines(lines)
    pages = [Page('index.md', 'Kurt Reference', None, [], 1)]
    used = {'index'}
    for i, line in enumerate(lines):
        m = TOP.match(line) if i not in code else None
        if m:
            slug = base = page_slug(m.group(1), m.group(2))
            k = 2
            while slug in used:
                slug, k = f'{base}-{k}', k + 1
            used.add(slug)
            pages.append(Page(slug + '.md', f'{m.group(1)}. {m.group(2)}', m.group(1), [], i + 1))
        pages[-1].lines.append(line)
    for page in pages:
        page_code = code_block_lines(page.lines)
        for i, line in enumerate(page.lines):
            h = HEADING.match(line)
            if h and i not in page_code:
                n = NUMBERED.match(h.group(2))
                if n:
                    page.anchors.add(anchor(n.group(1)))
    return pages


def section_index(pages: list[Page]) -> dict[str, tuple[str, str | None]]:
    """Each section number -> (its page, its anchor; None for the top of a page)."""
    index: dict[str, tuple[str, str | None]] = {}
    for page in pages:
        for a in page.anchors:
            number = a[len('sec-'):].replace('-', '.')
            index[number] = (page.file, None if number == page.number else a)
    return index


def link_target(target: tuple[str, str | None], here: str) -> str:
    file, a = target
    if file == here:
        return '#' + a if a else '#'
    return file + ('#' + a if a else '')


FOREIGN = re.compile(r'\.md`?(?:\s|,|-|–|and\b|or\b|§\d+(?:\.\d+)*)*$')   # `doc/kurt-soundness.md §8.41-§8.42`


def link_sections(prose: str, before: str, index, here: str) -> str:
    """The `§N.M` of this document in a stretch of prose (not in code) as links; one that follows the
    name of another document (`doc/kurt-kernel.md §8`) stays text."""
    out, last = [], 0
    for m in SECREF.finditer(prose):
        number = m.group(1)
        context = (before + prose[:m.start()])[-300:]
        if number in index and not FOREIGN.search(context):
            out.append(prose[last:m.start()])
            out.append(f'[§{number}]({link_target(index[number], here)})')
            last = m.end()
    out.append(prose[last:])
    return ''.join(out)


def repo_path(path: str, root: Path) -> str | None:
    """`path` if it names a public file or directory of the repository (or a bare `kurt-*.md` of doc/)."""
    path = path.rstrip('/.')
    if re.fullmatch(r'kurt-[\w-]+\.md', path):
        path = 'doc/' + path
    if not path or path.startswith(PRIVATE) or path == 'doc/kurt-ref.md' or '..' in path:
        return None
    return path if (root / path).exists() else None


def github_url(path: str, root: Path) -> str:
    return GITHUB + ('tree/main/' if (root / path).is_dir() else 'blob/main/') + path


def link_paths(prose: str, root: Path) -> str:
    def repl(m):
        p = repo_path(m.group(1), root)
        return f'[{m.group(1)}]({github_url(p, root)})' if p else m.group(0)
    return PATHLIKE.sub(repl, prose)


def rewrite_line(line: str, before: str, index, here: str, root: Path) -> str:
    """A line of prose: section references and repository paths as links, code spans unchanged
    (a code span that is just a path becomes a link with the code as its text)."""
    out, last = [], 0
    for m in CODESPAN.finditer(line):
        prose = line[last:m.start()]
        out.append(link_paths(link_sections(prose, before + line[:last], index, here), root))
        p = repo_path(m.group(2), root) if re.fullmatch(r'[\w./-]+', m.group(2)) else None
        out.append(f'[{m.group(0)}]({github_url(p, root)})' if p else m.group(0))
        last = m.end()
    prose = line[last:]
    out.append(link_paths(link_sections(prose, before + line[:last], index, here), root))
    return ''.join(out)


TEXT_BLOCK = re.compile(r'(kurt(\s|$)|python|cd |pip |lean |lake |\$ |>>> |\{"|[A-Z][a-z]+Error:|\w[\w.-]*\.kurt[: ])')


def block_language(block: list[str]) -> str:
    """`kurt` for Kurt source (and its output, which reads the same), `text` for shell commands, JSON,
    Python sessions and error messages."""
    first = next(line for line in block if line.strip()).strip()
    return 'text' if TEXT_BLOCK.match(first) else 'kurt'


def page_markdown(page: Page, index, root: Path) -> str:
    """The page as MkDocs Markdown: its headings one level up (its section is the page's `#`), with
    explicit anchors for the numbered ones, links, fenced code blocks."""
    lines = page.lines
    code = code_block_lines(lines)
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if i in code:
            block = []
            while i < len(lines) and i in code:
                block.append(lines[i][4:])
                i += 1
            while block and not block[-1].strip():
                block.pop()
            fence = '````' if any(b.lstrip().startswith('```') for b in block) else '```'
            out += [f'{fence}{block_language(block)}', *block, fence, '']
            continue
        h = HEADING.match(line)
        if h:
            level = len(h.group(1)) - 1
            title = h.group(2)
            n = NUMBERED.match(title)
            attr = f' {{ #{anchor(n.group(1))} }}' if n else ''
            out.append('#' * level + ' ' + title + attr)
        elif page.number is None and line.startswith('# '):
            out.append(line)
        else:
            # Python-Markdown wants a blank line before a list (GitHub doesn't)
            if (re.match(r'([-*]|\d+\.) ', line) and out and out[-1].strip()
                    and not re.match(r'\s*([-*+]|\d+\.) ', out[-1]) and not out[-1].startswith((' ', '|'))):
                out.append('')
            before = '\n'.join(lines[max(0, i - 3):i]) + '\n'
            out.append(rewrite_line(line, before, index, page.file, root))
        i += 1
    return '\n'.join(out).rstrip() + '\n'


def kurt_version(root: Path) -> str:
    tree = ast.parse((root / 'src/kurt/kurt.py').read_text(encoding='utf-8'))
    for node in tree.body:
        if (isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'version' for t in node.targets)
                and isinstance(node.value, ast.Constant)):
            return str(node.value.value)
    return '?'


def kurt_keywords(root: Path) -> list[str]:
    tree = ast.parse((root / 'src/kurt/kurt.py').read_text(encoding='utf-8'))
    for node in tree.body:
        if (isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == 'keywords'
                and isinstance(node.value, ast.Dict)):
            return [str(key.value) for key in node.value.keys if isinstance(key, ast.Constant)]
    return []


def build_pages(text: str, root: Path = ROOT) -> dict[str, str]:
    """kurt-ref.md as the pages of the site: {file name: Markdown}, in the order of the doc."""
    pages = split_reference(text)
    index = section_index(pages)
    result = {}
    for page in pages:
        md = page_markdown(page, index, root)
        if page.number is None:
            md += (f'\n---\n\nThis site is generated from [`doc/kurt-ref.md`]({GITHUB}blob/main/doc/kurt-ref.md) of '
                   f'Kurt {kurt_version(root)}. Try Kurt in the browser: [the playground]({PLAYGROUND_URL}).\n')
        result[page.file] = md
    return result


def mkdocs_config(pages: list[Page], version: str, site_url: str, hook: Path) -> dict:
    return {
        'site_name': f'Kurt {version} Reference',
        'site_url': site_url,
        'site_description': 'The reference of Kurt, a proof language for students',
        'repo_url': 'https://github.com/harmeling/kurt-lang',
        'repo_name': 'harmeling/kurt-lang',
        'edit_uri': '',
        'docs_dir': 'docs',
        'use_directory_urls': True,
        'nav': [{('Start' if p.number is None else p.title.replace('`', '')): p.file} for p in pages]
               + [{'Playground': PLAYGROUND_URL}],
        'theme': {
            'name': 'material',
            'font': False,                       # no Google Fonts: the system's fonts, nothing from elsewhere
            'features': ['navigation.footer', 'navigation.top', 'navigation.tracking', 'toc.follow',
                         'search.highlight', 'search.suggest', 'content.code.copy'],
            'palette': [
                {'media': '(prefers-color-scheme: light)', 'scheme': 'default', 'primary': 'indigo',
                 'toggle': {'icon': 'material/brightness-7', 'name': 'Switch to dark mode'}},
                {'media': '(prefers-color-scheme: dark)', 'scheme': 'slate', 'primary': 'indigo',
                 'toggle': {'icon': 'material/brightness-4', 'name': 'Switch to light mode'}},
            ],
        },
        'plugins': [{'search': {'lang': 'en'}}],
        'hooks': [str(hook)],
        'markdown_extensions': [
            'tables', 'attr_list', 'md_in_html',
            {'toc': {'permalink': True}},
            {'pymdownx.highlight': {'use_pygments': True}},
            'pymdownx.superfences',
        ],
    }


# --- the Kurt lexer for Pygments, registered when MkDocs loads this file as a hook ----------------

def make_kurt_lexer(keywords: list[str]):
    # (Pygments comes with mkdocs-material, not with Kurt: imported by name, so that the type check needs neither)
    lexer, token = importlib.import_module('pygments.lexer'), importlib.import_module('pygments.token')
    RegexLexer, words = lexer.RegexLexer, lexer.words
    Comment, Keyword, Name, Number, String, Text, Operator, Punctuation = (
        token.Comment, token.Keyword, token.Name, token.Number, token.String, token.Text, token.Operator, token.Punctuation)

    declarations = ['var', 'const', 'infix', 'postfix', 'prefix', 'brackets', 'arity', 'bindop', 'chain',
                    'flat', 'sym', 'prop', 'calc', 'alias', 'sort', 'default', 'everything', 'builtin']
    commands = sorted(set(keywords) - set(declarations) | {'with', 'local'})

    class KurtLexer(RegexLexer):
        name = 'Kurt'
        aliases = ['kurt']
        filenames = ['*.kurt']
        tokens = {
            'root': [
                (r';.*$', Comment.Single),
                (r'"[^"\n]*"', String),
                (r"(\$\$?|%%?)[A-Za-zͰ-Ͽ][A-Za-z0-9]*'*", Name.Variable),
                (words(declarations, prefix=r'(?<![\w$%])', suffix=r'\b'), Keyword.Declaration),
                (words(('todo',), prefix=r'(?<![\w$%])', suffix=r'\b'), Keyword.Pseudo),
                (words(('true', 'false', 'contradiction'), prefix=r'(?<![\w$%])', suffix=r'\b'), Keyword.Constant),
                (words(commands, prefix=r'(?<![\w$%])', suffix=r'\b'), Keyword),
                (r'\b\d+(\.\d+)?\b', Number),
                (r'[()\[\]{},]', Punctuation),
                (r'[^\w\s"();,\[\]{}$%]+', Operator),
                (r'\w+', Text),
                (r'\s+', Text),
                (r'.', Text),
            ]
        }
    return KurtLexer


def register_kurt_lexer(root: Path = ROOT) -> None:
    """Make `kurt` a language of Pygments (for ```kurt blocks) without installing a package: a module
    in sys.modules and its entry in Pygments' table of lexers."""
    import types
    _mapping = importlib.import_module('pygments.lexers._mapping')
    module = types.ModuleType('kurt_reference_lexer')
    setattr(module, 'KurtLexer', make_kurt_lexer(kurt_keywords(root)))
    setattr(module, '__all__', ['KurtLexer'])
    sys.modules[module.__name__] = module
    _mapping.LEXERS['KurtLexer'] = (module.__name__, 'Kurt', ('kurt',), ('*.kurt',), ('text/x-kurt',))


def on_config(config, **kwargs):          # the MkDocs hook
    register_kurt_lexer(Path(os.environ.get('KURT_REFERENCE_ROOT', ROOT)))
    return config


# --- the command ----------------------------------------------------------------------------------

def write_project(project: Path, root: Path, site_url: str) -> None:
    text = (root / 'doc/kurt-ref.md').read_text(encoding='utf-8')
    pages = split_reference(text)
    docs = project / 'docs'
    docs.mkdir(parents=True, exist_ok=True)
    for name, md in build_pages(text, root).items():
        (docs / name).write_text(md, encoding='utf-8')
    config = mkdocs_config(pages, kurt_version(root), site_url, Path(__file__).resolve())
    # JSON is YAML: no quoting problems with the titles
    (project / 'mkdocs.yml').write_text(json.dumps(config, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def trim(out: Path) -> None:
    """Leave out what the site doesn't need (from ~3.2 MB to ~1 MB): the source maps of Material's
    scripts and styles, and the search's support of languages other than English (lunr/)."""
    import shutil
    for path in out.rglob('*.map'):
        path.unlink()
    shutil.rmtree(out / 'assets/javascripts/lunr', ignore_errors=True)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=(__doc__ or '').split('\n')[0])
    ap.add_argument('--out', default=str(ROOT / 'site/reference'), help='the site (default: site/reference)')
    ap.add_argument('--pages', metavar='DIR', help='only write the MkDocs project (mkdocs.yml, docs/) to DIR')
    ap.add_argument('--site-url', default=SITE_URL)
    ap.add_argument('--strict', action='store_true', help='a warning of MkDocs (e.g. a broken link) is an error')
    args = ap.parse_args(argv)
    if args.pages:
        write_project(Path(args.pages), ROOT, args.site_url)
        print(f'wrote the MkDocs project to {args.pages}')
        return 0
    if not (importlib.util.find_spec('mkdocs') and importlib.util.find_spec('material')):
        print('mkdocs-material is not installed: pip install mkdocs-material', file=sys.stderr)
        return 1
    out = Path(args.out).resolve()
    with tempfile.TemporaryDirectory() as tmp:
        write_project(Path(tmp), ROOT, args.site_url)
        cmd = [sys.executable, '-m', 'mkdocs', 'build', '--quiet', '--clean', '-f', str(Path(tmp) / 'mkdocs.yml'),
               '-d', str(out)] + (['--strict'] if args.strict else [])
        env = dict(os.environ, KURT_REFERENCE_ROOT=str(ROOT), NO_MKDOCS_2_WARNING='true')   # (Material's banner)
        result = subprocess.run(cmd, env=env)
    if result.returncode == 0:
        trim(out)
        print(f'the reference site in {out}')
    return result.returncode


if __name__ == '__main__':
    sys.exit(main())
