import unittest
import kurt
from examples import examples

class Test_Parsing(unittest.TestCase):
    def test_parsing(self):
        kurt.load_file('all.kurt', kurt.initial_kb)
        kurt.initial_kb.format = 'sexpr'
        n = len(examples)
        passed = 0
        for i in range(n):
            (input_line, _, true_output) = examples[i]    # pick input, parsed
            try:
                ts = kurt.PG(kurt.scan_string(input_line))     # peekable token stream
                pt = kurt.parse_tokenstream(ts, kurt.initial_kb)[0]  # parse tree
                output = kurt.expr_str(pt, kurt.initial_kb)
            except Exception as e:
                output = (str(e).split('\n'))[-1]    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

if __name__ == '__main__':
    unittest.main()