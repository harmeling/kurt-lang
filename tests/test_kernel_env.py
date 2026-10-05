import contextlib
import copy
import io
import unittest

import kurt.kurt as kurt

# the kernel sees a knowledge base only through `KernelEnv`: read-only, only the lookups it needs,
# each answer fixed for the whole check


class TestKernelEnv(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            self.kb = kurt.load_file('set', self.kb)

    def test_read_only(self):
        env = kurt.KernelEnv(self.kb)
        with self.assertRaises(AttributeError):
            env.format = 'sexpr'
        with self.assertRaises(RuntimeError):
            env.add_const('x')                      # not a lookup the kernel may use
        with self.assertRaises(RuntimeError):
            env.theory_append

    def test_answers_stay_fixed(self):
        env = kurt.KernelEnv(self.kb)
        self.assertFalse(env.is_const('zzz'))
        self.kb.add_const('zzz')                      # a change during the check isn't seen
        self.assertFalse(env.is_const('zzz'))
        self.assertTrue(kurt.KernelEnv(self.kb).is_const('zzz'))
        facts = list(env.all_theory())
        self.kb.add_const('yyy')
        self.assertEqual(len(list(env.all_theory())), len(facts))
        sig = env.bool_sig('in')
        sig.append(99)                               # a copy: the next answer is the same
        self.assertEqual(env.bool_sig('in'), self.kb.bool_sig('in'))

if __name__ == '__main__':
    unittest.main()
