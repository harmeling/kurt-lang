import unittest
import copy
import kurt.kurt as kurt
from .examples import examples

class Test_Parsing(unittest.TestCase):
    def test_parsing(self):
        kb = copy.deepcopy(kurt.initial_kb)
        kurt.load_file('numbers.kurt', kb)
        kb.format = 'sexpr'
        for i in range(len(examples)):
            (input_line, _, true_output) = examples[i]               # pick input, parsed
            try:
                ts = kurt.PeekableGenerator(kurt.scan_string(input_line, kurt.initial_kb))           # peekable token stream
                _, pt, _, _ = kurt.parse_tokenstream(ts, kb)         # parse tree
                output = kurt.expr_str(pt[0], kb)
            except Exception as e:
                output = (str(e).split('\n'))[-1]                    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

if __name__ == '__main__':
    unittest.main()