import unittest
import sys
import os

# Add the parent directory to the path to import kurt
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import kurt

class TestGenerateAllCombinations(unittest.TestCase):
    
    def setUp(self):
        self.kb = kurt.initial_kb

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
        
        # Should have exactly one combination: the whole expression
        self.assertEqual(len(combinations), 1)
        expr_a, expr_A = combinations[0]
        self.assertEqual(expr_a, self.token_a)
        self.assertEqual(expr_A, self.token_x)
    
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
            if expr_a != None:
                if kurt.equal_expr(expr_a, self.token_a):
                    found_a = True
                    expected_A: kurt.Expr = [self.token_plus, self.token_x, self.token_b]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A))
                    break
        self.assertTrue(found_a, "Should be able to extract 'a' from 'a + b'")
        
        # Check that we can extract 'b'
        found_b = False
        for expr_a, expr_A in combinations:
            if expr_a != None:
                if kurt.equal_expr(expr_a, self.token_b):
                    found_b = True
                    expected_A: kurt.Expr = [self.token_plus, self.token_a, self.token_x]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A))
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
            if expr_a != None:
                if kurt.equal_expr(expr_a, inner_expr):
                    found_bc = True
                    expected_A: kurt.Expr = [self.token_plus, self.token_a, self.token_x]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A))
                    break
        self.assertTrue(found_bc, "Should be able to extract '(b + c)' from 'a + (b + c)'")
        
        # Should be able to extract 'c' from deep inside
        found_c = False
        for expr_a, expr_A in combinations:
            if expr_a != None:
                if kurt.equal_expr(expr_a, self.token_c):
                    found_c = True
                    # expr_A should be a + (b + $x)
                    expected_inner: kurt.Expr = [self.token_plus, self.token_b, self.token_x]
                    expected_A: kurt.Expr = [self.token_plus, self.token_a, expected_inner]
                    self.assertTrue(kurt.equal_expr(expr_A, expected_A))
                    break
        self.assertTrue(found_c, "Should be able to extract 'c' from 'a + (b + c)'")
    
    def test_with_expr_a_constraint(self):
        """Test with constraint on expr_a"""
        expr: kurt.Expr = [self.token_plus, self.token_a, self.token_b]
        # Only look for combinations where expr_a is 'a'
        combinations = list(kurt.generate_all_combinations(expr, self.token_x, self.token_a, self.kb))
        
        # Should only return combinations where expr_a equals 'a'
        for expr_a, expr_A in combinations:
            if expr_a is not None:
                self.assertTrue(kurt.equal_expr(expr_a, self.token_a))
    
    def test_all_single_hole_decompositions(self):
        """Test the helper function directly"""
        expr: kurt.Expr = [self.token_plus, self.token_a, self.token_b]
        decompositions = list(kurt.all_single_hole_decompositions(expr, self.token_x))
        
        # Should have decompositions for:
        # - whole expression: (a + b, $x)
        # - operator: (+, $x a b)  
        # - first operand: (a, $x + b)
        # - second operand: (b, a + $x)
        
        self.assertGreaterEqual(len(decompositions), 3)
        
        # Check specific decompositions
        subterms = [subterm for subterm, _ in decompositions]
        hole_exprs = [hole_expr for _, hole_expr in decompositions]
        
        # Should be able to extract 'a'
        self.assertIn(self.token_a, subterms)
        # Should be able to extract 'b' 
        self.assertIn(self.token_b, subterms)
        # Should be able to extract the whole expression
        self.assertTrue(any(kurt.equal_expr(st, expr) for st in subterms))
    
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
        self.assertTrue(kurt.equal_expr(new_expr, expected))
        
        # Test replace deep inside
        new_expr = kurt.replace_at_path(expr, [2, 2], self.token_x)
        expected = [self.token_plus, self.token_a, [self.token_plus, self.token_b, self.token_x]]
        self.assertTrue(kurt.equal_expr(new_expr, expected))
    
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

if __name__ == '__main__':
    unittest.main()