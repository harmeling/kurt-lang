import io
import copy
import unittest
import kurt.kurt as kurt
import contextlib

from tests.utils import PROJECT_ROOT

# the lessons of tutorial/ and keywords/ are lessons, not tests (prose, not fixed expected
# output, see CLAUDE.md) -- so we only check that each one still loads cleanly, i.e. that none of
# them has bit-rotted into a `KurtException` as the language keeps changing


class TestLessons(unittest.TestCase):
    def check(self, folder: str):
        lesson_paths = sorted((PROJECT_ROOT / folder).glob("*.kurt"))
        self.assertTrue(lesson_paths, f"No `.kurt` files found under {folder}/")
        for i, path in enumerate(lesson_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                out_buf, err_buf = io.StringIO(), io.StringIO()
                try:
                    with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                        _ = kurt.load_file(str(path), kb, main=False)
                except kurt.KurtException as e:
                    self.fail(f'{path.name} no longer loads cleanly: {e.msg}')

    def test_tutorial(self):
        self.check('tutorial')

    def test_keywords(self):
        self.check('keywords')

if __name__ == '__main__':
    unittest.main()
