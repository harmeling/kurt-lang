import contextlib
import copy
import io
import os
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt

# a `todo` inside a block whose content is discarded (`sandbox`, `expect`, `break`) is no open
# `todo` of the file -- one in a block that closes with a result is


class TestTodoDiscarded(unittest.TestCase):
    def todos(self, text: str) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'f.kurt')
            with open(path, 'w') as fh:
                fh.write(text)
            old = kurt.run_state.kurtc_enabled
            kurt.run_state.kurtc_enabled = False
            try:
                with contextlib.redirect_stdout(io.StringIO()), open(path, encoding='utf-8') as f:
                    bundle = kurt.checked_exports(path, f, Path(path), copy.deepcopy(kurt.initial_kb), False)
            finally:
                kurt.run_state.kurtc_enabled = old
        return bundle.todos

    def test_discarded(self):
        self.assertEqual(self.todos('load prop\nsandbox\n    todo true\nconst z\n'), [])
        self.assertEqual(self.todos('load prop\nexpect "ProofError"\n    todo true\n    false\nconst z\n'), [])

    def test_kept(self):
        self.assertEqual(len(self.todos('load prop\nshow %A ⇒ %A\nproof\n    todo\n    %A ⇒ %A\nqed\n')), 1)
        self.assertEqual(len(self.todos('load prop\nassume %A\n    todo %B\nconst z\n')), 1)
        self.assertEqual(len(self.todos('load prop\ntodo %A\n')), 1)

if __name__ == '__main__':
    unittest.main()
