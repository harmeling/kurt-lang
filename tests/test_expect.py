import contextlib
import copy
import io
import os
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# `expect "KIND" "TEXT"`: the block must raise an error of that kind whose message contains the
# text -- and two files that the proof tests can't check with `expect` themselves


def check(path: str) -> str:
    # the error of checking the file, or '' if it checks
    old = kurt.run_state.kurtc_enabled
    kurt.run_state.kurtc_enabled = False
    try:
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            kurt.load_file(path, copy.deepcopy(kurt.initial_kb), main=True)
    except kurt.KurtException as e:
        return e.msg
    finally:
        kurt.run_state.kurtc_enabled = old
    return ''

def check_text(text: str) -> str:
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'f.kurt')
        with open(path, 'w', encoding='utf-8') as f:
            f.write(text)
        return check(path)


class TestExpect(unittest.TestCase):
    def test_text(self):
        self.assertEqual(check_text('load prop\nexpect "ProofError" "can not derive `false`"\n    false\ntrue\n'), '')
        self.assertIn('without that text', check_text('load prop\nexpect "ProofError" "something else"\n    false\ntrue\n'))
        self.assertIn('got a different error', check_text('load prop\nexpect "EvalError" "can not derive"\n    false\ntrue\n'))
        self.assertIn('takes a string', check_text('load prop\nexpect "ProofError" 3\n    false\n'))

    def test_empty_expect_is_not_confirmed(self):
        msg = check(str(PROJECT_ROOT / 'proofs' / 'soundness' / 'helpers' / 'empty-expect.kurt'))
        self.assertIn('ExpectationError: this `expect "ProofError"` block finished without raising a `ProofError`', msg)

    def test_minimal_can_not_be_loaded(self):
        # minimal.kurt is the core, which Kurt reads when it starts (`read_core`): never loaded
        msg = check(str(PROJECT_ROOT / 'src' / 'kurt' / 'theories' / 'minimal.kurt'))
        self.assertIn('is the core, which every file starts with', msg)
        kb = copy.deepcopy(kurt.initial_kb)
        with self.assertRaises(kurt.KurtException):
            kurt.load_file('minimal', kb)

if __name__ == '__main__':
    unittest.main()
