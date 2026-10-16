import io
import json
import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT, numbered

# all errors (`--all-errors`, `RunConfig(all_errors=True)`, the editors): after an error in the main
# file, checking goes on -- a formula that can't be derived is admitted, a block that doesn't close
# is closed anyway, any other line is dropped; the result stays failed

ALL = kurt.RunConfig(all_errors=True)

TWO_FORMULAS = '''load prop
bool A, B, C, D
use A implies B
use A
B
C
D
B and C
todo A and C
'''


def check(text: str, config: kurt.RunConfig = ALL, name: str = 'proof.kurt') -> kurt.CheckResult:
    return kurt.Session(config).check_text(text, name=name)


class TestAllErrors(unittest.TestCase):
    def test_independent_errors_are_all_found(self):
        result = check(TWO_FORMULAS)
        self.assertFalse(result.ok)
        self.assertEqual([(e['kind'], e['line']) for e in result.errors], [('ProofError', 6), ('ProofError', 7)])
        self.assertEqual((result.error_kind, result.error_line), ('ProofError', 6))    # the first
        self.assertIn('can not derive `C`', result.error)
        # the lines after them are checked: `C` is admitted, so line 8 follows from it
        self.assertTrue(numbered(result.output, 8, 'by and-intro(5, 6 (todo))'), result.output)
        self.assertIn('Proof not checked: 2 errors.', result.output)
        self.assertLess(result.output.index('can not derive `C`'), result.output.index('B and C'))   # at its place
        # admitted internally: only the real `todo` is one
        self.assertEqual(len(result.todos), 1)
        self.assertIn('A and C', result.todos[0])
        # an event for each, at its place
        kinds = [(e['kind'], e['line']) for e in result.events if e['kind'] == 'error' or e['line'] == 8]
        self.assertEqual(kinds, [('error', 6), ('error', 7), ('step', 8)])

    def test_without_it_the_first_error_stops(self):
        result = check(TWO_FORMULAS, kurt.RunConfig())
        self.assertFalse(result.ok)
        self.assertEqual([e['line'] for e in result.errors], [6])
        self.assertNotIn('Proof not checked', result.output)
        self.assertFalse(numbered(result.output, 8, 'by and-intro(5, 6 (todo))'))

    def test_a_proof_that_does_not_reach_its_goal(self):
        # its claim is admitted, and the line that ends it has its own content
        text = 'load prop\nbool A, B, C\nuse A\nshow A and C\nproof\n    A\nB or C\nA and C\n'
        result = check(text)
        said = [(e['line'], next(l for l in e['message'].splitlines() if l.startswith('ProofError'))) for e in result.errors]
        self.assertEqual(said, [(4, 'ProofError: the proof of `A and C` (line 4) ends at line 7 without reaching its goal -- can not derive `C`'),
                                (7, 'ProofError: can not derive `B or C`')])
        self.assertEqual(len(result.errors), 2)
        self.assertTrue(numbered(result.output, 8, 'by 4'), result.output)        # the admitted claim

    def test_a_qed_that_fails(self):
        text = 'load prop\nbool A, C\nuse A\nshow A and C\nproof\n    A\nqed\nA and C\n'
        result = check(text)
        self.assertEqual([e['line'] for e in result.errors], [4])         # at the claim
        self.assertIn('ends at line 7 without reaching its goal', result.error)
        self.assertTrue(numbered(result.output, 8, 'by 4'), result.output)

    def test_an_unreached_goal_is_the_claims_error(self):
        # also without all errors: at the `show` (the editors mark that line), with what is missing
        result = check('load prop\nbool A, C\nuse A\nshow A and C\nproof\n    A\nA\n', kurt.RunConfig())
        self.assertEqual((result.error_kind, result.error_line), ('ProofError', 4))
        self.assertIn('show A and C', result.error)
        self.assertIn('the proof of `A and C` (line 4) ends at line 7 without reaching its goal -- can not derive `C`', result.error)
        self.assertIsNotNone(result.failure)             # (why, as data: for the editors)
        # an `expect` still sees it as a `ProofError` that can't derive the goal
        expected = check('load prop\nbool A, C\nuse A\nexpect "ProofError" "can not derive `C`"\n    show A and C\n    proof\n        A\nA\n', kurt.RunConfig())
        self.assertTrue(expected.ok, expected.error)

    def test_an_error_inside_nested_blocks(self):
        text = '''load prop
bool A, B, C
use A
show B implies A
proof
    assume B
        C
        A
D
'''
        result = check(text)
        self.assertEqual([e['line'] for e in result.errors], [7, 9])
        self.assertIn('B implies A', result.output)

    def test_an_unreadable_show_skips_its_proof(self):
        text = 'load prop\nbool A, C\nuse A\nshow A and and C\nproof\n    A\n    C\nC\n'
        result = check(text)
        self.assertEqual([(e['kind'], e['line']) for e in result.errors], [('ParseError', 4), ('ProofError', 8)])

    def test_a_failed_line_that_opens_a_block_skips_it(self):
        text = 'load prop\nbool A, B\nuse A\npick x with B\n    A\nB\n'
        result = check(text)
        self.assertEqual([e['line'] for e in result.errors], [4, 6])

    def test_the_end_of_the_file(self):
        # a proof not finished, and a claim without proof: both errors, at their claims
        unfinished = check('load prop\nbool A, C\nuse A\nshow C\nproof\n    A\n')
        self.assertEqual([e['line'] for e in unfinished.errors], [4])
        self.assertIn("isn't finished at the end of the file", unfinished.error)
        both = check('load prop\nbool A, B, C\nuse A\nB\nshow C\n')
        self.assertEqual([e['line'] for e in both.errors], [4, 5])
        self.assertIn('Proof not checked: 2 errors.', both.output)

    def test_expect_is_unchanged(self):
        confirmed = check('load prop\nbool A, B\nexpect "ProofError"\n    B\nuse A\nA\n')
        self.assertTrue(confirmed.ok, confirmed.error)
        # an `expect` whose error doesn't come stops, as without all errors
        missed = check('load prop\nbool A, B\nuse A\nexpect "ProofError"\n    A\nB\n')
        self.assertEqual([e['line'] for e in missed.errors], [6])
        self.assertIn('ExpectationError', missed.error)

    def test_an_error_in_a_loaded_file_stops(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, 'broken.kurt'), 'w', encoding='utf-8') as stream:
                stream.write('bool P\nP\n')
            text = 'load broken\nbool A\nA\nA\n'
            result = kurt.Session(kurt.RunConfig(all_errors=True, untrusted_paths=(tmp,))).check_text(text, name=os.path.join(tmp, 'main.kurt'))
            self.assertEqual(len(result.errors), 1)
            self.assertIn('broken.kurt', result.error)

    def test_strict_mode_reports_each_use(self):
        text = 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n'
        result = check(text, kurt.RunConfig(all_errors=True, strict=True))
        lines = [e['line'] for e in result.errors]
        self.assertEqual(lines[:2], [3, 4])
        self.assertTrue(all(e['kind'] == 'EvalError' for e in result.errors[:2]))

    def test_the_command_line(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'two.kurt')
            with open(path, 'w', encoding='utf-8') as stream:
                stream.write(TWO_FORMULAS)
            env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
            run = subprocess.run([sys.executable, '-m', 'kurt', '-a', path], capture_output=True, text=True, cwd=tmp, env=env)
            self.assertEqual(run.returncode, 1)
            self.assertEqual(run.stderr.count('ProofError: can not derive'), 2)
            self.assertIn('Proof not checked: 2 errors.', run.stdout)
            self.assertTrue(numbered(run.stdout, 8, 'by and-intro(5, 6 (todo))'), run.stdout)
            self.assertFalse(os.path.exists(path + 'c'))         # no `.kurtc` with errors
            # the result as JSON: all of them
            run = subprocess.run([sys.executable, '-m', 'kurt', '--json', '--all-errors', path], capture_output=True, text=True, cwd=tmp, env=env)
            self.assertEqual(run.returncode, 1)
            self.assertEqual([e['line'] for e in json.loads(run.stdout)['errors']], [6, 7])
            # without it, the first one only
            run = subprocess.run([sys.executable, '-m', 'kurt', path], capture_output=True, text=True, cwd=tmp, env=env)
            self.assertEqual((run.returncode, run.stderr.count('ProofError')), (1, 1))

    def test_an_error_that_stops_the_file_ends_with_the_summary(self):
        # the end of the file inside a statement: with `-a`, the summary was missing, and the error
        # named the line after the end ("started around line 4"; 2026-10-14, found by the docs hunt)
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'eof.kurt')
            with open(path, 'w', encoding='utf-8') as stream:
                stream.write('bool A, B\nA\nfoo ( bar\n')
            env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
            run = subprocess.run([sys.executable, '-m', 'kurt', '-a', '--no-kurtc', path], capture_output=True, text=True, cwd=tmp, env=env)
            self.assertEqual(run.returncode, 1)
            self.assertIn('the statement that started at line 3', run.stderr)
            self.assertIn('Proof not checked: 2 errors.', run.stdout)

    def test_no_kurtc_for_a_claim_without_proof(self):
        # (a `.kurtc` was written before the end of the file was checked)
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'claim.kurt')
            with open(path, 'w', encoding='utf-8') as stream:
                stream.write('load prop\nbool A\nuse A\nA\nshow A\n')
            env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
            run = subprocess.run([sys.executable, '-m', 'kurt', path], capture_output=True, text=True, cwd=tmp, env=env)
            self.assertEqual(run.returncode, 1)
            self.assertIn('has no proof', run.stderr)
            self.assertFalse(os.path.exists(path + 'c'))

    def test_the_language_server_shows_all(self):
        server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
        published = []
        server.publish_diagnostics = lambda uri, diagnostics, version: published.append(diagnostics)
        uri = 'file:///tmp/two.kurt'
        server.texts[uri] = TWO_FORMULAS
        server.check(uri)
        errors = [d for d in published[-1] if d['severity'] == 1]
        self.assertEqual([d['range']['start']['line'] for d in errors], [5, 6])
        self.assertTrue(errors[0]['message'].startswith('ProofError: can not derive `C`'))
        # ... and the reasons of the lines after them
        self.assertIn(7, server.line_events(uri))
        # `allErrors: false`: the first one only
        server.all_errors = False
        server.check(uri)
        self.assertEqual(len([d for d in published[-1] if d['severity'] == 1]), 1)


if __name__ == '__main__':
    unittest.main()
