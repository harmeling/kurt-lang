import copy
import unittest

import kurt.kurt as kurt
from kurt.kurt import Token, generate_all_combinations, initial_kb
from tests.utils import with_quantifiers

class TestGenerateAllCombinations(unittest.TestCase):
    
    def setUp(self):
        self.kb = copy.deepcopy(kurt.initial_kb)    # (not the shared one: the tests mustn't change it)

        # Create test tokens
        self.token_x = kurt.Token('SYMBOL', '$x')
        self.token_a = kurt.Token('SYMBOL', 'a')
        self.token_b = kurt.Token('SYMBOL', 'b')
        self.token_c = kurt.Token('SYMBOL', 'c')
        self.token_plus = kurt.Token('SYMBOL', '+')
        
    def test_single_atom(self):
        """Test with a single atom"""
        expr = self.token_a
        combinations = list(kurt.generate_all_combinations(expr, self.token_x, None, self.kb))

        # Two combinations: substitute the whole atom (%A=$x, $a=a), or don't substitute at
        # all (%A=a unchanged, $a unconstrained -- the zero-occurrence case, see
        # doc/kurt-soundness.md #6)
        self.assertEqual(len(combinations), 2)
        substituting = [c for c in combinations if c[1] == self.token_x]
        self.assertEqual(len(substituting), 1)
        expr_a, expr_A = substituting[0]
        self.assertEqual(expr_a, self.token_a)
        self.assertEqual(expr_A, self.token_x)
        zero_occurrence = [c for c in combinations if c[1] != self.token_x]
        self.assertEqual(len(zero_occurrence), 1)
        expr_a, expr_A = zero_occurrence[0]
        self.assertIsNone(expr_a)
        self.assertEqual(expr_A, self.token_a)
    
    def test_simple_binary_expression(self):
        """Test with a + b"""
        expr: kurt.Expr = [self.token_plus, self.token_a, self.token_b]
        combinations = list(kurt.generate_all_combinations(expr, self.token_x, None, self.kb))
        
        # Should have 3 combinations:
        # 1. (a + b, $x)
        # 2. (a, $x + b) 
        # 3. (b, a + $x)
        # 4. (+, $x a b) - depending on implementation
        
        self.assertGreaterEqual(len(combinations), 3)
        
        # Check that we can extract 'a'
        found_a = False
        for expr_a, expr_A in combinations:
            if expr_a is not None:
                if kurt.equal_expr(expr_a, self.token_a, self.kb):
                    found_a = True
                    expected_A: kurt.Expr = [self.token_plus, self.token_x, self.token_b]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A, self.kb))
                    break
        self.assertTrue(found_a, "Should be able to extract 'a' from 'a + b'")
        
        # Check that we can extract 'b'
        found_b = False
        for expr_a, expr_A in combinations:
            if expr_a is not None:
                if kurt.equal_expr(expr_a, self.token_b, self.kb):
                    found_b = True
                    expected_A: kurt.Expr = [self.token_plus, self.token_a, self.token_x]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A, self.kb))
                    break
        self.assertTrue(found_b, "Should be able to extract 'b' from 'a + b'")
    
    def test_nested_expression(self):
        """Test with a + (b + c)"""
        inner_expr: kurt.Expr = [self.token_plus, self.token_b, self.token_c]
        expr: kurt.Expr = [self.token_plus, self.token_a, inner_expr]
        combinations = list(kurt.generate_all_combinations(expr, self.token_x, None, self.kb))
        
        # Should be able to extract (b + c) as a subterm
        found_bc = False
        for expr_a, expr_A in combinations:
            if expr_a is not None:
                if kurt.equal_expr(expr_a, inner_expr, self.kb):
                    found_bc = True
                    expected_A: kurt.Expr = [self.token_plus, self.token_a, self.token_x]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A, self.kb))
                    break
        self.assertTrue(found_bc, "Should be able to extract '(b + c)' from 'a + (b + c)'")
        
        # Should be able to extract 'c' from deep inside
        found_c = False
        for expr_a, expr_A in combinations:
            if expr_a is not None:
                if kurt.equal_expr(expr_a, self.token_c, self.kb):
                    found_c = True
                    # expr_A should be a + (b + $x)
                    expected_inner: kurt.Expr = [self.token_plus, self.token_b, self.token_x]
                    expected_A: kurt.Expr = [self.token_plus, self.token_a, expected_inner]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A, self.kb))
                    break
        self.assertTrue(found_c, "Should be able to extract 'c' from 'a + (b + c)'")
    
    def test_with_expr_a_constraint(self):
        """Test with constraint on expr_a"""
        expr: kurt.Expr = [self.token_plus, self.token_a, self.token_b]
        # Only look for combinations where expr_a is 'a'
        combinations = list(kurt.generate_all_combinations(expr, self.token_x, self.token_a, self.kb))
        
        # Should only return combinations where expr_a equals 'a' -- and return the one that
        # replaces it (not nothing: an empty list passed the loop below)
        for expr_a, expr_A in combinations:
            if expr_a is not None:
                self.assertTrue(kurt.equal_expr(expr_a, self.token_a, self.kb))
        expected_A: kurt.Expr = [self.token_plus, self.token_x, self.token_b]
        self.assertTrue(any(kurt.equal_expr(expr_A, expected_A, self.kb) for _, expr_A in combinations), combinations)
    
    def test_all_single_hole_decompositions(self):
        """Test the helper function directly"""
        expr: kurt.Expr = [self.token_plus, self.token_a, self.token_b]
        decompositions = list(kurt.all_single_hole_decompositions(expr, self.token_x, self.kb))
        
        # Should have decompositions for:
        # - whole expression: (a + b, $x)
        # - operator: (+, $x a b)  
        # - first operand: (a, $x + b)
        # - second operand: (b, a + $x)
        
        self.assertGreaterEqual(len(decompositions), 3)
        
        # Check specific decompositions
        subterms = [subterm for subterm, _ in decompositions]
        
        # Should be able to extract 'a'
        self.assertIn(self.token_a, subterms)
        # Should be able to extract 'b' 
        self.assertIn(self.token_b, subterms)
        # Should be able to extract the whole expression
        self.assertTrue(any(kurt.equal_expr(st, expr, self.kb) for st in subterms))
    
    def test_path_functions(self):
        """Test the path manipulation helper functions"""
        expr = [self.token_plus, self.token_a, [self.token_plus, self.token_b, self.token_c]]
        
        # Test get_at_path
        self.assertEqual(kurt.get_at_path(expr, []), expr)
        self.assertEqual(kurt.get_at_path(expr, [0]), self.token_plus)
        self.assertEqual(kurt.get_at_path(expr, [1]), self.token_a)
        self.assertEqual(kurt.get_at_path(expr, [2, 1]), self.token_b)
        self.assertEqual(kurt.get_at_path(expr, [2, 2]), self.token_c)
        
        # Test replace_at_path
        new_expr = kurt.replace_at_path(expr, [1], self.token_x)
        expected = [self.token_plus, self.token_x, [self.token_plus, self.token_b, self.token_c]]
        self.assertTrue(kurt.equal_expr(new_expr, expected, self.kb))
        
        # Test replace deep inside
        new_expr = kurt.replace_at_path(expr, [2, 2], self.token_x)
        expected = [self.token_plus, self.token_a, [self.token_plus, self.token_b, self.token_x]]
        self.assertTrue(kurt.equal_expr(new_expr, expected, self.kb))
    
    def test_iter_nodes(self):
        """Test the node iteration function"""
        expr: kurt.Expr = [self.token_plus, self.token_a, self.token_b]
        nodes = list(kurt.iter_nodes(expr))
        
        # Should have nodes for: whole expr, +, a, b
        self.assertEqual(len(nodes), 4)
        
        paths = [path for path, _ in nodes]
        node_exprs = [node for _, node in nodes]
        
        # Check paths
        self.assertIn([], paths)  # root
        self.assertIn([0], paths)  # operator
        self.assertIn([1], paths)  # first operand
        self.assertIn([2], paths)  # second operand
        
        # Check nodes
        self.assertIn(expr, node_exprs)  # whole expression
        self.assertIn(self.token_plus, node_exprs)
        self.assertIn(self.token_a, node_exprs)
        self.assertIn(self.token_b, node_exprs)


# the examples of `generate_all_combinations` (until 2026-11-02 in tests/test_gen_all_combinations.py):
# each example looks like this:
#   [expr,
#    [list of possible outputs of generate_all_combinations]]
#
# every example's `(None, expr)` entry is the zero-occurrence combination (`%A` doesn't have
# to mention `$x` at all, so `%A == expr` unchanged and `$a` is unconstrained) -- see
# doc/kurt-soundness.md #6 for why that candidate has to exist. Besides replacing one
# occurrence, a value occurring several times is also replaced at all of its occurrences at
# once (e.g. `(17, [g, $%1, $%1])`), and at some of them (two or more, `h 17 17 17` below) -- see
# `all_single_hole_decompositions`. The hole is at an operator position only for an operator that
# yields a term (`f` of `f 17`; todo 31), never at a boolean one or a binder (`forall`): it ranges
# over statements and terms (`hole_nodes`, soundness §8.40).
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
    # forall $z f $z -- `forall` as logic.kurt declares it (`with_quantifiers`: the core has no
    # quantifiers), so this exercises the bound-variable-aware behavior
    [[Token(label='SYMBOL', value='forall'), Token(label='SYMBOL', value='$z'), [Token(label='SYMBOL', value='f'), Token(label='SYMBOL', value='$z')]],
     ['($z, [forall, $%1, [f, $z]])',
      '([forall, $z, [f, $z]], $%1)',
      '(f, [forall, $z, [$%1, $z]])',
      '(None, [forall, $z, [f, $z]])']]

     ]

class TestCombinationExamples(unittest.TestCase):
    def test_combinations(self):
        for i in range(len(examples)):
            input = examples[i][0]
            true_output: list[str] = examples[i][1]
            try:
                token_x = Token(label='SYMBOL', value='$%1')   # use a variable name that doesn't appear in the examples
                # the renaming is usually done elsewhere
                kb = with_quantifiers(copy.deepcopy(initial_kb))
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