import unittest
import copy
import kurt.kurt as kurt
from .examples import examples

class Test_Parsing(unittest.TestCase):
    def test_parsing(self):
        kb = copy.deepcopy(kurt.initial_kb)
        kurt.load_file('number.kurt', kb)
        kb.format = 'sexpr'
        # the reading only, not the type check: with the sorts of number.kurt (todo 34), `432 422`
        # (a number applied to a number) is no number, and `f 178 + 432 422` a type error
        from unittest import mock
        patch = mock.patch.object(kurt, 'type_check_expression', lambda e, kb, bound_sorts=None: None)
        patch.start()
        self.addCleanup(patch.stop)
        for i in range(len(examples)):
            (input_line, _, true_output) = examples[i]               # pick input, parsed
            try:
                ts = kurt.PeekableGenerator(kurt.scan_string(input_line, kurt.initial_kb))           # peekable token stream
                _, pt, _, _ = kurt.parse_tokenstream(ts, kb)         # parse tree
                output = ', '.join(kurt.expr_str(e, kb) for e in pt)   # (all of them: `a, b` is two)
            except Exception as e:
                output = (str(e).split('\n'))[-1]                    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

if __name__ == '__main__':
    unittest.main()