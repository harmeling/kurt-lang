import io
import copy
import unittest
import kurt
import contextlib

from tests.utils import PROJECT_ROOT
tutorial_root = PROJECT_ROOT / "tutorial"

class TestTutorial(unittest.TestCase):
    def test_tutorial_lessons_run(self):
        # unlike proofs/, tutorial/*.kurt files carry no `;;; ` marker (they are
        # lesson prose, not fixed expected-output tests, see CLAUDE.md) -- so we
        # only check that each lesson still loads cleanly, i.e. that none of them
        # has bit-rotted into a `KurtException` as the language keeps changing.
        lesson_paths = sorted(tutorial_root.glob("*.kurt"))
        self.assertTrue(lesson_paths, "No `.kurt` files found under tutorial/")

        for i, path in enumerate(lesson_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                out_buf, err_buf = io.StringIO(), io.StringIO()
                try:
                    with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                        _ = kurt.load_file(str(path), kb, mainstream=False)
                except kurt.KurtException as e:
                    self.fail(f'{path.name} no longer loads cleanly: {e.msg}')

if __name__ == '__main__':
    unittest.main()
