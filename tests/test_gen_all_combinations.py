import unittest
import copy
from kurt import Token, generate_all_combinations, initial_kb

# each example looks like this:
#   [expr,
#    [list of possible outputs of generate_all_combinations]]
#
# every example's `(None, expr)` entry is the zero-occurrence combination (`%A` doesn't have
# to mention `$x` at all, so `%A == expr` unchanged and `$a` is unconstrained) -- see
# doc/kurt-soundness.md #6 for why that candidate has to exist. Besides replacing one
# occurrence, a value occurring several times is also replaced at all of its occurrences at
# once (e.g. `(17, [g, $%1, $%1])`), but not in any other combination (`old_examples` below
# still has those too, which were dropped for performance) -- see
# `all_single_hole_decompositions`.
examples = [
    # f 17
    [[Token(label='SYMBOL', value='f'), Token(label='INT', value='17')],
     ['([f, 17], $%1)',
      '(f, [$%1, 17])',
      '(17, [f, $%1])',
      '(None, [f, 17])']],

    # g 17 17
    [[Token(label='SYMBOL', value='g'), Token(label='INT', value='17'), Token(label='INT', value='17')],
     ['([g, 17, 17], $%1)',
      '(g, [$%1, 17, 17])',
      '(17, [g, $%1, 17])',
      '(17, [g, 17, $%1])',
      '(17, [g, $%1, $%1])',
      '(None, [g, 17, 17])']],

    # h 17 42
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='42')],
     ['([h, 17, 42], $%1)',
      '(h, [$%1, 17, 42])',
      '(17, [h, $%1, 42])',
      '(42, [h, 17, $%1])',
      '(None, [h, 17, 42])']],

    # h 17 42 17
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='42'), Token(label='INT', value='17')],
     ['([h, 17, 42, 17], $%1)',
      '(h, [$%1, 17, 42, 17])',
      '(17, [h, $%1, 42, 17])',
      '(42, [h, 17, $%1, 17])',
      '(17, [h, 17, 42, $%1])',
      '(17, [h, $%1, 42, $%1])',
      '(None, [h, 17, 42, 17])']],

    # h 17 17 17
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='17'), Token(label='INT', value='17')],
     ['([h, 17, 17, 17], $%1)',
      '(h, [$%1, 17, 17, 17])',
      '(17, [h, $%1, 17, 17])',
      '(17, [h, 17, $%1, 17])',
      '(17, [h, 17, 17, $%1])',
      '(17, [h, $%1, $%1, $%1])',
      '(17, [h, $%1, $%1, 17])',     # some of the occurrences (two or more, not all)
      '(17, [h, $%1, 17, $%1])',
      '(17, [h, 17, $%1, $%1])',
      '(None, [h, 17, 17, 17])']],

    # h $z
    [[Token(label='SYMBOL', value='h'), Token(label='SYMBOL', value='$z')],
     ['([h, $z], $%1)',
      '(h, [$%1, $z])',
      '($z, [h, $%1])',
      '(None, [h, $z])']],

    # h $x
    [[Token(label='SYMBOL', value='h'), Token(label='SYMBOL', value='$x')],
     ['([h, $x], $%1)',
      '(h, [$%1, $x])',
      '($x, [h, $%1])',
      '(None, [h, $x])']],

    # more examples where we check that $a does not contain freely any bound variables of $A
    # forall $z f $z -- `forall` is declared a bindop in `initial_kb` itself now (it used not
    # to be, in a bare `initial_kb`), so this exercises the real bound-variable-aware behavior;
    # see the second `forall` example below for the same input with more commentary
    [[Token(label='SYMBOL', value='forall'), Token(label='SYMBOL', value='$z'), [Token(label='SYMBOL', value='f'), Token(label='SYMBOL', value='$z')]],
     ['($z, [forall, $%1, [f, $z]])',
      '([forall, $z, [f, $z]], $%1)',
      '(f, [forall, $z, [$%1, $z]])',
      '(forall, [$%1, $z, [f, $z]])',
      '(None, [forall, $z, [f, $z]])']]

     ]

old_examples = [
    # f 17
    [[Token(label='SYMBOL', value='f'), Token(label='INT', value='17')], 
     ['([f, 17], $%1)',
      '(f, [$%1, 17])',
      '(17, [f, $%1])',
      '(None, [f, 17])']],

    # g 17 17
    [[Token(label='SYMBOL', value='g'), Token(label='INT', value='17'), Token(label='INT', value='17')],
     ['([g, 17, 17], $%1)',
      '(g, [$%1, 17, 17])',
      '(17, [g, $%1, $%1])',
      '(17, [g, $%1, 17])',
      '(17, [g, 17, $%1])',
      '(None, [g, 17, 17])']],

    # h 17 42
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='42')],
     ['([h, 17, 42], $%1)',
      '(h, [$%1, 17, 42])',
      '(17, [h, $%1, 42])',
      '(42, [h, 17, $%1])',
      '(None, [h, 17, 42])']],

    # h 17 42 17
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='42'), Token(label='INT', value='17')],
     ['([h, 17, 42, 17], $%1)',
      '(h, [$%1, 17, 42, 17])',
      '(17, [h, $%1, 42, 17])',
      '(42, [h, 17, $%1, 17])',
      '(17, [h, 17, 42, $%1])',
      '(17, [h, $%1, 42, $%1])',
      '(None, [h, 17, 42, 17])']],

    # h 17 17 17 
    [[Token(label='SYMBOL', value='h'), Token(label='INT', value='17'), Token(label='INT', value='17'), Token(label='INT', value='17')],
     ['([h, 17, 17, 17], $%1)',
      '(h, [$%1, 17, 17, 17])',
      '(17, [h, $%1, 17, 17])',
      '(17, [h, 17, $%1, 17])',
      '(17, [h, 17, 17, $%1])',
      '(17, [h, $%1, 17, $%1])',
      '(17, [h, 17, $%1, $%1])',
      '(17, [h, $%1, $%1, 17])',
      '(17, [h, $%1, $%1, $%1])',
      '(None, [h, 17, 17, 17])']],

    # h $z
    [[Token(label='SYMBOL', value='h'), Token(label='SYMBOL', value='$z')],
     ['([h, $z], $%1)',
      '(h, [$%1, $z])',
      '($z, [h, $%1])',
      '(None, [h, $z])']],

    # h $x
    [[Token(label='SYMBOL', value='h'), Token(label='SYMBOL', value='$x')],
     ['([h, $x], $%1)',
      '(h, [$%1, $x])',
      '($x, [h, $%1])',
      '(None, [h, $x])']],

     ]

class Test_Combinations(unittest.TestCase):
    def test_combinations(self):
        for i in range(len(examples)):
            input = examples[i][0]
            true_output: list[str] = examples[i][1]
            try:
                token_x = Token(label='SYMBOL', value='$%1')   # use a variable name that doesn't appear in the examples
                # the renaming is usually done elsewhere
                kb = copy.deepcopy(initial_kb)
                result = generate_all_combinations(input, token_x, None, kb)
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