import os
import sys
import io
import copy
import unittest
import kurt
import pathlib
import contextlib

def file_last_line(fname):
    # the last line in the file starts with `;;; ` and contains the expected last line of the output
    with open(fname, "r") as f:
        return f.readlines()[-1].strip()[4:]

def str_last_line(s):
    return s.strip().split('\n')[-1]

class TestProving(unittest.TestCase):
    def test_proving(self):
        example_paths = sorted(pathlib.Path("proofs").rglob("*.kurt"))
        # Optional: make sure we actually found something to test
        self.assertTrue(example_paths, "No .kurt files found under proofs/")

        for i, path in enumerate(example_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                true_last_line = file_last_line(str(path))
                out_buf, err_buf = io.StringIO(), io.StringIO()
                try:
                    with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                        _ = kurt.load_file(str(path), kb, mainstream=False)
                        print("Proof checked.")
                    actual_last_line = str_last_line(out_buf.getvalue())

                except kurt.KurtException as e:
                    # stderr was redirected in the with-block, so use what was captured.
                    actual_last_line = str_last_line(err_buf.getvalue() or e.msg)

                self.assertEqual(actual_last_line, true_last_line)

# class Test_Proving(unittest.TestCase):
#     def test_proving(self):
#         examples = list(pathlib.Path('proofs').rglob('*.kurt'))
# #        examples = list(pathlib.Path('proofs').rglob('simple-test.kurt'))
#         for i in range(len(examples)):
#             kb = copy.deepcopy(kurt.initial_kb)
#             fname = str(examples[i])
#             with self.subTest(msg=examples[i], i=i):
#                 try:
#                     true_last_line = file_last_line(fname)
#                     captured_stdout = io.StringIO()
#                     captured_stderr = io.StringIO()
#                     sys.stdout = captured_stdout                 # redirect stdout
#                     sys.stderr = captured_stderr                 # redirect stderr
#                     _ = kurt.load_file(fname, kb, mainstream=False)
#                     print('Proof checked.', file=sys.stdout)
#                     actual_last_line = str_last_line(captured_stdout.getvalue())
#                     self.assertEqual(actual_last_line, true_last_line)
#                 except kurt.KurtException as e:
#                     print(e.msg, file=sys.stderr)
#                     actual_last_line = str_last_line(captured_stderr.getvalue())
#                     self.assertEqual(actual_last_line, true_last_line)
#                 except AssertionError:
#                     raise
#                 except Exception as e:
#                     self.fail(f"Subtest {fname} failed with unexpected exception: {e}")                
#                 finally:
#                     sys.stdout = sys.__stdout__                  # reset redirect
#                     sys.stderr = sys.__stderr__                  # reset redirect

if __name__ == '__main__':
    unittest.main()