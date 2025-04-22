import os
import sys
import io
import copy
import unittest
import kurt
import pathlib

def file_last_line(fname):
    # the last line in the file starts with `;;; ` and contains the expected last line of the output
    with open(fname, "r") as f:
        return f.readlines()[-1].strip()[4:]

def str_last_line(s):
    return s.strip().split('\n')[-1]

class Test_Proving(unittest.TestCase):
    def test_proving(self):
        #kurt.initial_kb.format = 'sexpr'
        examples = list(pathlib.Path('proofs').rglob('*.kurt'))
        for i in range(len(examples)):
            kb = copy.deepcopy(kurt.initial_kb)
            fname = str(examples[i])
            with self.subTest(msg=examples[i], i=i):
                try:
                    true_last_line = file_last_line(fname)
                    captured_stdout = io.StringIO()
                    captured_stderr = io.StringIO()
                    sys.stdout = captured_stdout                 # redirect stdout
                    sys.stderr = captured_stderr                 # redirect stderr
                    _, success = kurt.load_file(fname, kb, mainstream=True)
                    if success:
                        print('Proof checked.', file=sys.stdout)
                        actual_last_line = str_last_line(captured_stdout.getvalue())
                    else:
                        actual_last_line = str_last_line(captured_stderr.getvalue())
                    self.assertEqual(actual_last_line, true_last_line)
                except kurt.KurtException as e:
                    print(e.msg, file=sys.stderr)
                    actual_last_line = str_last_line(captured_stderr.getvalue())
                    self.assertEqual(actual_last_line, true_last_line)
                except Exception as e:
                    self.fail(f"Subtest {fname} failed with unexpected exception: {e}")                
                finally:
                    sys.stdout = sys.__stdout__                  # reset redirect
                    sys.stderr = sys.__stderr__                  # reset redirect

if __name__ == '__main__':
    unittest.main()