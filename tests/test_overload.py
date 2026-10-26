import contextlib
import copy
import io
import unittest

import kurt.kurt as kurt


class TestOverload(unittest.TestCase):
    # overloading, stage 1 (decision 19 of dev/todo-sorts.md): the least sort of an application, as the
    # search (`top_sorts`) and the kernel (`k_value_sorts`) read it, and the declaration checks

    def setUp(self) -> None:
        self.kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kurt.load_file('complex.kurt', self.kb)

    def parse(self, text: str):
        ts = kurt.PeekableGenerator(kurt.scan_string(text, self.kb))
        _, trees, _, _ = kurt.parse_tokenstream(ts, self.kb)
        return trees[0]

    def test_profiles_are_one_chain(self):
        for op in ('+', '-', '*', '/', '^'):           # (`^` since todo 48: a complex power, natural-number exponents)
            self.assertEqual(self.kb.pos_sorts(op, 0), frozenset({'real', 'complex'}))
            self.assertEqual(self.kb.pos_sort(op, 0), 'complex')
            self.assertEqual(self.kb.pos_sort_least(op, 0), 'real')
        self.assertEqual(self.kb.pos_sorts('<', 1), frozenset({'real'}))

    def test_the_search_and_the_kernel_read_the_same_least_sort(self):
        for text, sort in [('1 + 2', 'real'), ('(1 + 2) * 3', 'real'), ('i + 1', 'complex'),
                           ('1 + (i * 2)', 'complex'), ('- 1', 'real'), ('- i', 'complex'), ('(1 / 2) + 3', 'real'),
                           ('2 ^ 3', 'real'), ('i ^ 2', 'complex'), ('(1 + i) ^ 2', 'complex'), ('2 ^ (1 / 2)', 'real')]:
            with self.subTest(text=text):
                e = self.parse(text)
                self.assertEqual(kurt.top_sorts(e, self.kb), {sort})
                self.assertEqual(kurt.k_value_sorts(e, kurt.KernelEnv(self.kb)), {sort})

    def test_a_signature_needs_one_chain_and_the_same_places(self):
        kb = copy.deepcopy(self.kb)
        kb.sorts.add('other')
        kb.sort_sigs['other'] = {}
        with self.assertRaisesRegex(kurt.KurtException, 'not in one chain'):
            kb.add_sort_signature('other', '+', [0, 1, 2])
        with self.assertRaisesRegex(kurt.KurtException, 'already has a `complex` signature'):
            kb.add_sort_signature('complex', '+', [0, 1, 2])


if __name__ == '__main__':
    unittest.main()
