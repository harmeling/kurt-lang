import io
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# what the robustness hunt of 2026-10-15 found: Python tracebacks where Kurt should give an error,
# a cache that made a clean file fail, and the exports crashing on shipped files

ENV = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src') + os.pathsep + os.environ.get('PYTHONPATH', ''))


def run_kurt(*args: str, stdin: str = '') -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, '-m', 'kurt', '--no-kurtc', *args], input=stdin,
                          env=ENV, capture_output=True, text=True, timeout=120)


class TestSharedCache(unittest.TestCase):
    def test_a_theory_from_another_runs_cache_keeps_its_variables_notes(self):
        # the language server shares the cache of checked theories among its sessions: the second
        # session's run didn't know the dependent variables (`$T` of `sum`) and the sorts of the
        # cached analysis.kurt, so argmax.kurt failed in the editor after a save, gauss.kurt crashed
        for name in ('proofs/analysis/argmax.kurt', 'proofs/natural-numbers/gauss.kurt'):
            with self.subTest(file=name):
                shared: dict = {}
                first = kurt.Session(kurt.RunConfig())
                first._state._checked_exports = shared
                self.assertTrue(first.check_file(str(PROJECT_ROOT / name)).ok)
                second = kurt.Session(kurt.RunConfig())
                second._state._checked_exports = shared
                result = second.check_file(str(PROJECT_ROOT / name))
                self.assertTrue(result.ok, result.error)

    def test_the_bundle_carries_the_notes(self):
        shared: dict = {}
        session = kurt.Session(kurt.RunConfig())
        session._state._checked_exports = shared
        self.assertTrue(session.check_text('load analysis\n').ok)
        bundles = [value[0] for value in shared.values()]
        self.assertTrue(any(b.dependent_vars for b in bundles), 'analysis.kurt has rules with dependent variables')
        self.assertTrue(all(b.origin_names for b in bundles if b.theory))     # (objects.kurt has no facts, only sorts)


class TestUnreadableFiles(unittest.TestCase):
    def test_a_binary_file_is_an_error_not_a_traceback(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'bin.kurt')
            with open(path, 'wb') as fh:
                fh.write(b'\xff\xfe\x00 not utf-8')
            result = kurt.check_file(path)
            self.assertFalse(result.ok)
            self.assertIn('is not a text file in UTF-8', result.error or '')
            loader = kurt.check_text('load bin\n', name=os.path.join(tmp, 'main.kurt'))
            self.assertIn('is not a text file in UTF-8', loader.error or '')

    def test_a_directory_is_an_error_not_a_traceback(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.mkdir(os.path.join(tmp, 'dir.kurt'))
            result = kurt.check_file(os.path.join(tmp, 'dir.kurt'))
            self.assertFalse(result.ok)
            self.assertIn('unable to read', result.error or '')


class TestExports(unittest.TestCase):
    def test_the_listing_of_an_inspection_keyword_is_not_a_line(self):
        # `kurt --latex keywords/02-use.kurt` died: "newlines not allowed in input_line" (26 shipped files)
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            Path(path).write_text('load propositional\nuse A "a"\nuse A implies B "ab"\ntheory\nuse\ninfix\nB\n', encoding='utf-8')
            for fmt in ('latex', 'markdown'):
                text = kurt.export_document(path, fmt, kurt.RunConfig())
                self.assertIn('ab', text)
                self.assertNotIn('level', text)                        # (the listing's lines)

    def test_lean_of_a_file_without_a_step_at_the_top_level(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            Path(path).write_text('load propositional\nprop A\nexpect "ProofError"\n    A\n', encoding='utf-8')
            text, _ = kurt.export_lean(path)
            self.assertIn('end Kurt', text)

    def test_an_unwritable_output_is_a_message(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            Path(path).write_text('load propositional\nuse A "a"\nA\n', encoding='utf-8')
            result = run_kurt('--latex', path, '-o', os.path.join(tmp, 'missing', 'p.tex'))
            self.assertEqual(result.returncode, 1)
            self.assertIn('could not write', result.stderr)
            self.assertNotIn('Traceback', result.stderr)


class TestShellAndEditor(unittest.TestCase):
    def test_save_without_a_string(self):
        for line in ('save 42', 'save x', 'save "a" "b"'):
            with self.subTest(line=line):
                result = kurt.check_text(f'load propositional\n{line}\n')
                self.assertEqual(result.error_kind, 'EvalError')
                self.assertIn('save', result.error or '')

    def test_a_search_that_matches_nothing_any_more(self):
        editor = kurt.LineEditor(['abc'])
        editor.start('> ')
        for key in ('ctrl-r', 'a', 'b', 'z'):
            editor.key(key)
        self.assertIsNone(editor.found)
        editor.render(80)                                   # (raised ValueError: substring not found)
        editor.key('backspace')
        self.assertEqual(editor.found, 0)


class TestLanguageServerTransport(unittest.TestCase):
    def test_malformed_messages_are_skipped(self):
        good = b'{"jsonrpc": "2.0", "method": "x"}'
        for bad in (b'garbage\r\n\r\n', b'Content-Length: abc\r\n\r\n', b'Content-Length: -5\r\n\r\n',
                    b'Content-Length: 5\r\n\r\n[1,2]', b'Content-Length: 3\r\n\r\n{"a', b'\xff\xfe\r\n\r\n'):
            with self.subTest(bad=bad):
                server = kurt.LanguageServer(io.BytesIO(bad + f'Content-Length: {len(good)}\r\n\r\n'.encode() + good), io.BytesIO())
                message = server.read()
                self.assertTrue(message is None or message == {'jsonrpc': '2.0', 'method': 'x'})
                self.assertIsNone(server.read())


class TestGeneratedLabels(unittest.TestCase):
    def test_a_users_label_enumeration_does_not_disturb_the_rules_of_a_set(self):
        # `use A ∧ B "enumeration"`, then `a ∈ {a, b}`: TypeError in `generate_enumeration_rules`;
        # `use A "element-1-of-2"` suppressed the rules for a pair
        text = 'load natural\nprop A, B\nuse A ∧ B "enumeration"\nuse A "element-1-of-2"\nconst a, b\na ∈ {a, b}\n'
        result = kurt.check_text(text)
        self.assertTrue(result.ok, result.error)



class TestDecisionsOfTheSecondHunt(unittest.TestCase):
    # what was decided on 2026-10-15 (dev/todo.md 45, 46, 48)

    def test_a_nul_byte_is_shown_escaped(self):
        result = kurt.check_text('load propositional\nprop A\nA\x00B\n')
        self.assertEqual(result.error_kind, 'ScanError')
        self.assertIn('`\\x00`', result.error or '')

    def test_the_caret_of_an_indentation_error_is_at_the_line(self):
        # it was drawn at the block's indentation, beyond the end of a short line
        result = kurt.check_text('load propositional\nexpect "EvalError"\nconst A\n')
        self.assertIn('\nconst A\n^\n', result.error or '')
        result = kurt.check_text('load propositional\nprop A\nuse A\nqed\n')
        self.assertIn('no block is open', result.error or '')
        self.assertIn('\nqed\n^\n', result.error or '')

    def test_help_with_a_keyword(self):
        result = kurt.check_text('help use\nhelp nonsense\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('use a formula without proof', result.output)
        self.assertIn('`nonsense` is not a keyword', result.output)

    def test_a_cited_line_that_is_only_admitted_says_so(self):
        # with --all-errors a failed line is admitted (`admit_line`), and later lines cited it as if proved
        result = kurt.check_text('load propositional\nprop A, B\nuse A implies B\ntodo A\nB\n')
        self.assertIn('; by 3(4 (todo))', result.output)
        session = kurt.Session(kurt.RunConfig(all_errors=True))
        result = session.check_text('load propositional\nprop A, B\nuse A implies B\nA\nB\n')
        self.assertFalse(result.ok)
        self.assertIn('; by 3(4 (todo))', result.output)

    def test_a_block_is_numbered_from_the_line_that_opened_it(self):
        # a `let x` without a condition adds no formula at its line: its result was numbered by its last line only
        result = kurt.check_text('load logic, equality\nshow forall $x ($x = $x)\nproof\n    let x\n        x = x\nqed\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('; 4-5 by forall-intro', result.output)

    def test_a_multi_place_rewrite_shows_only_the_step_it_uses(self):
        # `x + y = 0 + 0` from `x = 0`, `y = 0` showed `5a`-`5c`, all `y = (0 + 0)`, and used `5d`
        result = kurt.check_text('load numbers\nconst x, y\nuse x = 0\nuse y = 0\nx + y = 0 + 0\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('5a by', result.output)
        self.assertNotIn('5b', result.output)
        self.assertIn('; by equal-elim(4, 5a)', result.output)

    def test_a_relation_between_declared_variables_warns(self):
        import contextlib
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            result = kurt.check_text('load numbers\nvar a, b\nuse a <= b\nconst c\nuse c <= b\nuse $a <= $a\nuse a <= b implies b <= a\n')
        self.assertTrue(result.ok, result.error)
        warnings = [line for line in err.getvalue().splitlines() if 'holds for every value' in line]
        self.assertEqual(len(warnings), 1, err.getvalue())
        self.assertIn('`a <= b` holds for every value of the variables `a`, `b`', warnings[0])


class TestLeftoversOfTheSecondHunt(unittest.TestCase):
    # dev/todo.md 48 (2026-10-15): what was left after the decisions

    def test_the_main_file_may_be_any_existing_file(self):
        # `kurt notes.txt` tried `notes.txt.kurt`; a `load` still adds the extension
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'notes.txt')
            Path(path).write_text('load propositional\nprop A\nuse A\nA\n', encoding='utf-8')
            self.assertTrue(kurt.check_file(path).ok)
            self.assertIn('unable to open `notes.kurt`', kurt.check_text('load notes\n', name=os.path.join(tmp, 'm.kurt')).error or '')

    def test_no_warning_when_run_as_a_module_file(self):
        # `python3 -m kurt.kurt FILE` printed "'kurt.kurt' found in sys.modules after import of package 'kurt'"
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            Path(path).write_text('load propositional\nprop A\nuse A\nA\n', encoding='utf-8')
            result = subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', path], env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn('RuntimeWarning', result.stderr)
        self.assertIn('Proof checked', result.stdout)

    def test_the_hover_of_a_load_line_links_the_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = os.path.realpath(tmp)   # kurt resolves a loaded file's path; macOS's /tmp is a symlink
            Path(tmp, 'lib.kurt').write_text('load propositional\nprop P\nuse P "p"\n', encoding='utf-8')
            uri = 'file://' + os.path.join(tmp, 'h.kurt')
            server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
            server.publish_diagnostics = lambda uri, diagnostics, version: None
            server.texts[uri], server.versions[uri] = 'load propositional, equality\nload lib\nP\n', 1
            server.check(uri)
            def hover(line):
                found = server.hover({'textDocument': {'uri': uri}, 'position': {'line': line, 'character': 0}})
                assert found is not None, f'no hover at line {line}'
                return found['contents']['value']
            self.assertIn('[propositional.kurt](file://', hover(0))
            self.assertIn('[equality.kurt](file://', hover(0))
            self.assertIn(f'[lib.kurt]({Path(tmp, "lib.kurt").as_uri()})', hover(1))

    def test_load_names_separated_by_spaces_are_refused(self):
        # `load propositional numbers` loaded `numbers` only; `propositional` was dropped without a word
        result = kurt.check_text('load propositional numbers\n')
        self.assertEqual(result.error_kind, 'ScanError')
        self.assertIn('`load propositional, numbers`', result.error or '')
        self.assertTrue(kurt.check_text('load propositional, numbers\nload "propositional"\n').ok)

    def test_a_false_membership_fails_fast(self):
        # `1 ∈ {-1, 2}` after a set of three was used took 81 s: the multi-place rewrite took the
        # generated schema `$y2 ∈ {$y1, $y2}` as a base and tried to rewrite its variables into
        # numbers (`cannot_be_rewritten`); 6 s now -- a generous bound against a relapse
        import time
        start = time.monotonic()
        result = kurt.check_text('load natural\ncalc on\n2 ∈ {1, 2, 3}\nexpect "ProofError"\n    1 ∈ {-1, 2}\nexpect "ProofError"\n    5 ∈ {1, ..., 3}\n')
        self.assertTrue(result.ok, result.error)
        self.assertLess(time.monotonic() - start, 45)

    def test_many_case_blocks_with_many_rules_stay_fast(self):
        # n `case` blocks, each deriving `G` from one of n rules `Ai ∧ K ⇒ G`, with n unrelated
        # disjunctions and implications in scope (scripts/bench_case.py, 'blocks'): the premise
        # `Ai`, a plain symbol, was tried against the whole theory in each block -- cubic, 27 s at
        # n = 128 (3.4 s at 64); the index of the theory knows a symbol's bucket now, 1 s
        # (2026-10-16) -- a generous bound against a relapse
        import time
        n = 128
        alts = [f'A{i}' for i in range(n)]
        noise = [(f'B{j}', f'C{j}', f'H{j}') for j in range(n)]
        lines = ['load propositional', 'prop ' + ', '.join(alts + ['G', 'K'] + [s for t in noise for s in t]),
                 'use ' + ' or '.join(alts)]
        for b, c, h in noise:
            lines += [f'use {b} or {c}', f'use {b} implies {h}', f'use {c} implies {h}']
        lines += ['use K'] + [f'use {a} and K implies G' for a in alts]
        for a in alts:
            lines += [f'case {a}', '    G']
        lines += ['G']
        start = time.monotonic()
        result = kurt.check_text('\n'.join(lines) + '\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('case-elim', [row for row in result.output.splitlines() if re.match(r'\s*\d+  G\s', row)][-1])
        self.assertLess(time.monotonic() - start, 10)

    def test_a_rewriting_rule_for_statements_is_not_tried_with_a_term(self):
        # `guided_rewrite` binds the place `$b`/`%b` of a rewriting rule to a subterm directly:
        # "iff-subst" (`%a ⇔ %b`, statements) with a term as the place searched its premise through
        # the whole theory for nothing (2.7 s of 16 s in proofs/mafi1/28-self-adjoint.kurt) --
        # now only as the unifier would bind it (2026-10-16)
        tried: list[tuple[str, bool]] = []
        original = kurt.impl_elim

        def recorded(expr, free, formula, filename, s, kb):
            for value in s.subst.values():
                tried.append((formula.label, kurt.bool_expr(value, kb)))
            return original(expr, free, formula, filename, s, kb)

        kurt.impl_elim = recorded
        try:
            result = kurt.check_text('load logic, equality\nconst a, b, c\nprop P\nuse P a\nuse a = b\nexpect "ProofError"\n    P c\n')
        finally:
            kurt.impl_elim = original
        self.assertTrue(result.ok, result.error)
        self.assertIn(('equal-elim', False), tried)       # the place `c` is a term: for `$b` of "equal-elim" ...
        self.assertNotIn(('iff-subst', False), tried)     # ... but not for `%b` of "iff-subst"


if __name__ == '__main__':
    unittest.main()
