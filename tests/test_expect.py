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
    old = kurt.kurtc_enabled
    kurt.kurtc_enabled = False
    try:
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            kurt.load_file(path, copy.deepcopy(kurt.initial_kb), mainstream=True)
    except kurt.KurtException as e:
        return e.msg
    finally:
        kurt.kurtc_enabled = old
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
        # minimal.kurt is only for reference (the core is built into Kurt): its `false` makes sure
        msg = check(str(PROJECT_ROOT / 'src' / 'kurt' / 'theories' / 'minimal.kurt'))
        self.assertIn('ProofError: can not derive `false`', msg)

if __name__ == '__main__':
    unittest.main()
