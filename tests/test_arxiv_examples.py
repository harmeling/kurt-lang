import io
import copy
import unittest
import kurt.kurt as kurt
import contextlib

from tests.utils import PROJECT_ROOT

# dev/marketing/arxiv/examples/*.kurt are the standalone source files
# dev/marketing/arxiv/gen_examples.py renders into the arXiv paper's code listings (the
# other listings are literal excerpts of tutorial/, proofs/ and src/kurt/theories/,
# already covered by test_kurt_lessons.py and test_kurt_proofs.py). This only guards
# against bit-rot -- that they still load -- the same way test_kurt_lessons.py does for
# tutorial/keywords; it does not regenerate or check the paper's .tex output itself. Run
# dev/marketing/arxiv/gen_examples.py by hand after a change here or to kurt.py.


EXAMPLES = PROJECT_ROOT / 'dev' / 'marketing' / 'arxiv' / 'examples'


@unittest.skipUnless(EXAMPLES.is_dir(), 'the paper is not published (dev/ is private)')
class TestArxivExamples(unittest.TestCase):
    def test_examples_load(self):
        folder = 'dev/marketing/arxiv/examples'
        example_paths = sorted((PROJECT_ROOT / folder).glob("*.kurt"))
        self.assertTrue(example_paths, f"No `.kurt` files found under {folder}/")
        for i, path in enumerate(example_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                out_buf, err_buf = io.StringIO(), io.StringIO()
                try:
                    with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                        _ = kurt.load_file(str(path), kb, main=False)
                except kurt.KurtException as e:
                    self.fail(f'{path.name} no longer loads cleanly: {e.msg}')

    def test_rejected_examples_are_rejected(self):
        # examples/rejected/*.kurt show the paper's error messages (gen_examples.py, mode
        # "cli-error"): each must still be rejected, with the kind of error the paper shows
        folder = 'dev/marketing/arxiv/examples/rejected'
        expected = {'10-missing-step.kurt': 'ProofError', '11-counterexample.kurt': 'ProofError',
                    '12-sort-error.kurt': 'TypeError'}
        example_paths = sorted((PROJECT_ROOT / folder).glob("*.kurt"))
        self.assertEqual(sorted(p.name for p in example_paths), sorted(expected))
        for i, path in enumerate(example_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                out_buf, err_buf = io.StringIO(), io.StringIO()
                with self.assertRaises(kurt.KurtException) as caught:
                    with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                        _ = kurt.load_file(str(path), kb, main=False)
                self.assertEqual(caught.exception.kind, expected[path.name])


if __name__ == '__main__':
    unittest.main()
