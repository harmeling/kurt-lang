import os
import sys
import io
import copy
import unittest
import kurt

def last_line(fname):
    # the last line in the file starts with `;;; ` and contains the expected last line of the output
    with open(fname, "r") as f:
        return f.readlines()[-1].strip()[4:]

class Test_Proving(unittest.TestCase):
    def test_proving(self):
        #kurt.initial_kb.format = 'sexpr'
        path = "tests/proofs/"
        examples  = [f for f in os.listdir(path) if f.endswith(".kurt")]
        for i in range(len(examples)):
            kb = copy.deepcopy(kurt.initial_kb)
            fname = path + examples[i]
            with self.subTest(msg=examples[i], i=i):
                try:
                    true_last_line = last_line(fname)
                    capturedOutput = io.StringIO()
                    sys.stdout = capturedOutput                  # redirect stdout.
                    _, success = kurt.load_file(fname, kb, mainstream=True)
                    if not success:
                        actual_last_line = capturedOutput.getvalue().split('\n')[-1]
                        self.assertEqual(actual_last_line, true_last_line)
                except kurt.KurtException as e:  # Replace with the actual expected exception type
                    if e.msg.split('\n')[-1] != true_last_line:
                        self.fail(f'////\n{e.msg}\n////{true_last_line}\n////')                        
                except Exception as e:
                    self.fail(f"Subtest {fname} failed with exception: {e}")
                finally:
                    sys.stdout = sys.__stdout__                  # reset redirect.

if __name__ == '__main__':
    unittest.main()