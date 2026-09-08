import io
import copy
import unittest

import kurt

class _NoNamePath:
    # a minimal stand-in for a `Path`/`Traversable` whose `.open()` succeeds but returns a
    # file-like object with no `.name` -- `read_eval_loop` needs `.name` (every real file has
    # one), so evaluating this "file"'s contents raises a genuine `AttributeError`
    def __truediv__(self, name: str) -> "_NoNamePath":
        return self
    def open(self, encoding: str = 'utf-8') -> io.StringIO:
        return io.StringIO('true\n')
    def __str__(self) -> str:
        return '<no-name>'

class TestLoadFileExceptionNarrowing(unittest.TestCase):
    def test_attributeerror_during_evaluation_is_not_swallowed_as_file_not_found(self):
        # `load_file`'s per-candidate `except (FileNotFoundError, NotADirectoryError,
        # AttributeError): continue` used to wrap the *entire* open-and-evaluate block, so an
        # `AttributeError` raised while evaluating a successfully-opened file's contents
        # (a real bug, unrelated to whether the file exists) was silently reinterpreted as
        # "this candidate path doesn't have the file, try the next one" -- and once every
        # search path was exhausted, surfaced as a misleading `EvalError: unable to open ...`
        # instead of the real `AttributeError` and its traceback. This is exactly the failure
        # mode this test's own discovery hit: `_EmbeddedTheoryFile.open()` originally returned
        # a bare `io.StringIO` with no `.name`, and the resulting `AttributeError` from
        # `read_eval_loop` got masked the same way. Fixed by narrowing the guard to just the
        # `candidate.open(...)` call itself.
        kb = copy.deepcopy(kurt.initial_kb)
        with self.assertRaises(AttributeError):
            kurt.load_file('anything', kb, search_paths=[_NoNamePath()], mainstream=False)

if __name__ == '__main__':
    unittest.main()
