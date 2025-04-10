import unittest
from kurt import Token, generate_all_combinations

examples = [
     # f 17
    [[Token(label='SYMBOL', value='f'), Token(label='INT', value='17')], 
     ['([f, 17], $x)', '(f, [$x, 17])', '(17, [f, $x])', '(None, [f, 17])']],
     # g 17 17
    [[Token(label='SYMBOL', value='g'), Token(label='INT', value='17'), Token(label='INT', value='17')],
        ['([g, 17, 17], $x)', '(g, [$x, 17, 17])', '(17, [g, $x, $x])', '(17, [g, $x, 17])',
        '(17, [g, 17, $x])', '(None, [g, 17, 17])']],
        # h 17 42
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='42')],
        ['([h, 17, 42], $x)', '(h, [$x, 17, 42])', '(17, [h, $x, 42])', '(42, [h, 17, $x])',
        '(None, [h, 17, 42])']],
        # h 17 42 17
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='42'), Token(label='INT', value='17')],
        ['([h, 17, 42, 17], $x)', '(h, [$x, 17, 42, 17])', '(17, [h, $x, 42, 17])',
        '(42, [h, 17, $x, 17])', '(17, [h, 17, 42, $x])', '(17, [h, $x, 42, $x])', '(None, [h, 17, 42, 17])']],
        # h 17 17 17 
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='17'), Token(label='INT', value='17')],
        ['([h, 17, 17, 17], $x)', '(h, [$x, 17, 17, 17])', '(17, [h, $x, 17, 17])',
        '(17, [h, 17, $x, 17])', '(17, [h, 17, 17, $x])', '(17, [h, $x, 17, $x])',
        '(17, [h, 17, $x, $x])', '(17, [h, $x, $x, 17])', '(17, [h, $x, $x, $x])', '(None, [h, 17, 17, 17])']],
        # h $z
    [[Token(label='SYMBOL', value='h'), Token(label='SYMBOL', value='$z')],
        ['([h, $z], $x)', '(h, [$x, $z])', '($z, [h, $x])', '(None, [h, $z])']],
        # h $x
    [[Token(label='SYMBOL', value='h'), Token(label='SYMBOL', value='$x')],
        ['([h, $x], $x)', '(None, [h, $x])']],
        # more examples where we check that $a does not contain any bound variables of $A
     ]

class Test_Combinations(unittest.TestCase):
    def test_combinations(self):
        for i in range(len(examples)):
            input = examples[i][0]
            true_output: list[str] = examples[i][1]
            try:
                token_x = Token(label='SYMBOL', value='$x')
                result = generate_all_combinations(input, token_x, expr_a=None)
                output = [str(r) for r in result]
            except Exception as e:
                output = (str(e).split('\n'))[-1]    # this could be the desired result
            with self.subTest(msg=str(input), i=i):
                # compare the two lists of strings, the order does not matter
                output = sorted(output)
                true_output = sorted(true_output)
                self.assertEqual(output, true_output)

if __name__ == '__main__':
    unittest.main()