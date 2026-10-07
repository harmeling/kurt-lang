import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT


# Complete accepted contradictions from dev/astra-suggestions.md, not just error-message tests.
CONTRADICTIONS = {
    'self_reference': '''load prop
def liar iff not liar
assume liar
    not liar
    false
not liar
liar
false
''',
    'duplicate_batch': '''load prop
def p iff true, p iff false
p
false
''',
    'indirect_cycle': '''load prop
def p iff q, q iff not p
assume p
    q
    not p
    false
not p
q
p
false
''',
    'diagonal_argument': '''load prop
const rel
infix rel 50 50
def c rel $x iff not ($x rel $x)
assume c rel c
    not (c rel c)
    false
not (c rel c)
c rel c
false
''',
    'calculator_argument': '''load numbers
const plus
infix plus 60 60
calc plus add
def c plus $x = 0
c plus 0 = 0
c plus 1 = 0
calc on
c = 0
calc off
0 plus 1 = 0
calc on
1 = 0
0 ≠ 1
calc off
not (0 = 1)
0 = 1
(0 = 1) and not (0 = 1)
false
''',
    'calculator_head': '''load numbers
infix plus 60 60
calc plus add
def $x plus $y = 0
1 plus 0 = 0
calc on
1 = 0
0 ≠ 1
calc off
not (0 = 1)
false
''',
}


class TestDefinitionSoundness(unittest.TestCase):
    def test_complete_contradictions_are_rejected(self):
        for strict in (False, True):
            for name, source in CONTRADICTIONS.items():
                with self.subTest(strict=strict, proof=name):
                    result = kurt.Session(kurt.RunConfig(strict=strict)).check_text(source)
                    self.assertFalse(result.ok, result.output)
                    self.assertFalse(result.complete)
                    self.assertEqual(result.error_kind, 'EvalError', result.error)
                    self.assertNotIn('Proof checked', result.output)

    def test_strict_cli_rejects_contradictions(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'false.kurt'
            for name in ('self_reference', 'duplicate_batch', 'indirect_cycle', 'diagonal_argument'):
                with self.subTest(proof=name):
                    path.write_text(CONTRADICTIONS[name], encoding='utf-8')
                    run = subprocess.run([sys.executable, '-m', 'kurt', '--strict', '--json', '--no-kurtc', str(path)],
                                         env=dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src')),
                                         capture_output=True, text=True, timeout=30)
                    self.assertEqual(run.returncode, 1, run.stdout + run.stderr)
                    self.assertFalse(json.loads(run.stdout)['complete'])

    def test_aliases_cannot_hide_recursion_or_redefinition(self):
        for definition in ('def p iff not q', 'def p iff true, q iff false'):
            with self.subTest(definition=definition):
                result = kurt.Session(kurt.RunConfig(strict=True)).check_text('load prop\nalias q p\n' + definition + '\n')
                self.assertFalse(result.ok, result.output)
                self.assertEqual(result.error_kind, 'EvalError', result.error)

    def test_rejected_batch_leaves_no_definitions_or_declarations(self):
        for strict in (False, True):
            for bad in ('def p iff true, p iff false', 'def p iff true, q iff not q',
                        'def p iff q, q iff not p'):
                with self.subTest(strict=strict, definition=bad):
                    shell = kurt.Shell(kurt.RunConfig(strict=strict))
                    self.assertTrue(shell.start_text('load prop\n').ok)
                    self.assertIn('EvalError', shell.feed(bad))
                    with shell.session._active():
                        self.assertFalse(shell.kb.is_const('p'))
                        self.assertFalse(shell.kb.is_const('q'))
                        self.assertFalse(shell.kb.is_bool('p'))
                        self.assertFalse(shell.kb.is_bool('q'))
                    self.assertIn('Error', shell.feed('p'))
                    self.assertNotIn('Error', shell.feed('def p iff true\np'))

    def test_conservative_definitions_still_work(self):
        sources = [
            'load group\ndef $a ∘ $b = $a\n',
            'load prop\ndef p iff true, q iff p\np\nq\n',
            'load numbers\ndef square($x) = $x * $x\ncalc on\nsquare(3) = 9\n',
            'load equality\nbrackets ⟨ ⟩\nconst b\ndef q = ⟨b, b⟩\nq = ⟨b, b⟩\n',
            'load prop\ndef negate(%A) iff not %A\nnegate(true) iff not true\n',
        ]
        for strict in (False, True):
            for source in sources:
                with self.subTest(strict=strict, source=source):
                    result = kurt.Session(kurt.RunConfig(strict=strict)).check_text(source)
                    self.assertTrue(result.complete, result.error)


if __name__ == '__main__':
    unittest.main()
