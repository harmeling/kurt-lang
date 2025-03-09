import unittest
import kurt

path = 'example-proofs/'
examples = [
    'and-intro.kurt',
    'equal-elim.kurt',
    'forall-intro.kurt',
    'impl-elim.kurt',
    'proof-a.kurt',
    'proof-b.kurt',
    'proof-c.kurt',
    'proof-by-contradiction.kurt',
    'show-proof-qed.kurt']

class Test_Proving(unittest.TestCase):
    def test_proving(self):
        #kurt.initial_kb.format = 'sexpr'
        n = len(examples)
        passed = 0
        for i in range(n):
            try:
                output = ''
                fname = path + examples[i]
                kurt.load_file(fname, kurt.initial_kb)
                output = 'Everything is ok!'
            except Exception as e:
                output = (str(e).split('\n'))[-1]
            with self.subTest(msg=fname, i=i):
                print(output)
                self.assertEqual(output, 'Everything is ok!')

if __name__ == '__main__':
    unittest.main()