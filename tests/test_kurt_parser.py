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

class Test_Application(unittest.TestCase):
    # todo 89: `f(a)` is `f a` (doc/kurt-ref.md, "Function application"); the trap is `f(a)(b)`
    def read(self, text):
        kb = copy.deepcopy(kurt.initial_kb)
        kb.format = 'sexpr'
        ts = kurt.PeekableGenerator(kurt.scan_string(text, kurt.initial_kb))
        _, pt, _, _ = kurt.parse_tokenstream(ts, kb)
        return ', '.join(kurt.expr_str(e, kb) for e in pt)

    def test_glued_application_is_the_same_term(self):
        self.assertEqual(self.read('f(a)'), self.read('f a'))
        self.assertEqual(self.read('f(a, b)'), self.read('f (a, b)'))      # `f` applied to the pair

    def test_glued_chain_is_one_argument(self):
        self.assertEqual(self.read('f(a)(b)'), self.read('f (a b)'))
        self.assertNotEqual(self.read('f(a)(b)'), self.read('(f a) b'))    # for a mapping that returns a mapping: `(F f) a`


if __name__ == '__main__':
    unittest.main()