import unittest
import sys
import os

# Add the parent directory to the path to import kurt
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import kurt

class TestNonFlatSymmetricOperators(unittest.TestCase):
    
    def setUp(self):
        self.kb = kurt.KnowledgeBase()
        # Define a non-flat symmetric operator
        self.kb.add_infix('~', 15, 15)  # some operator with equal precedence
        self.kb.add_sym('~')            # make it symmetric
        # Note: we don't add it to flat, so it remains non-flat
        
        # Create test tokens
        self.token_a = kurt.Token('SYMBOL', 'a')
        self.token_b = kurt.Token('SYMBOL', 'b')
        self.token_c = kurt.Token('SYMBOL', 'c')
        self.token_tilde = kurt.Token('SYMBOL', '~')
        
        # Variables for pattern matching
        self.var1 = kurt.Token('SYMBOL', '$$var1')
        self.var2 = kurt.Token('SYMBOL', '$$var2')
        
    def test_symmetric_operator_properties(self):
        """Test that our operator is correctly configured"""
        self.assertTrue(self.kb.is_sym('~'))
        self.assertFalse(self.kb.is_flat('~'))
        self.assertTrue(self.kb.is_infix('~'))
        
    def test_match_symmetric_same_length_direct(self):
        """Test matching symmetric operator with same length - direct order"""
        # Pattern: $$var1 ~ $$var2
        pattern: kurt.Expr = [self.token_tilde, self.var1, self.var2]
        
        # Expression: a ~ b
        expr: kurt.Expr = [self.token_tilde, self.token_a, self.token_b]
        
        subst = {}
        blocked = frozenset()
        unify_flag = False
        
        results = list(kurt.match_exprs_to_patterns(
            [(expr, pattern)], subst, blocked, unify_flag, self.kb))
        
        # Should find matches for both orientations due to symmetry
        self.assertGreaterEqual(len(results), 1)
        
        # Check that we can match a~b against $$var1~$$var2
        found_direct = any(
            r.get('$$var1') == self.token_a and r.get('$$var2') == self.token_b
            for r in results
        )
        self.assertTrue(found_direct, "Should match a~b with $$var1=a, $$var2=b")
        
    def test_match_symmetric_same_length_swapped(self):
        """Test matching symmetric operator with same length - swapped order"""
        # Pattern: $$var1 ~ $$var2  
        pattern: kurt.Expr = [self.token_tilde, self.var1, self.var2]
        
        # Expression: a ~ b
        expr: kurt.Expr = [self.token_tilde, self.token_a, self.token_b]
        
        subst = {}
        blocked = frozenset()
        unify_flag = False
        
        results = list(kurt.match_exprs_to_patterns(
            [(expr, pattern)], subst, blocked, unify_flag, self.kb))
        
        # Should find matches for both orientations due to symmetry
        self.assertGreaterEqual(len(results), 1)
        
        # Check that we can match a~b against $$var1~$$var2 in swapped order
        found_swapped = any(
            r.get('$$var1') == self.token_b and r.get('$$var2') == self.token_a
            for r in results
        )
        self.assertTrue(found_swapped, "Should match a~b with $$var1=b, $$var2=a (swapped)")
        
    def test_match_symmetric_different_length_fails(self):
        """Test that non-flat symmetric operators require same length"""
        # Pattern: $$var1 ~ $$var2 (2 operands)
        pattern: kurt.Expr = [self.token_tilde, self.var1, self.var2]
        
        # Expression: [~, a, b, c] (has 3 operands)
        # This should NOT match because non-flat operators require exact length
        expr = [self.token_tilde, self.token_a, self.token_b, self.token_c]
        
        subst = {}
        blocked = frozenset()
        unify_flag = False
        
        results = list(kurt.match_exprs_to_patterns([(expr, pattern)], subst, blocked, unify_flag, self.kb))
        
        # Should not match because lengths are different (2 vs 2, but structure differs)
        # The pattern expects 2 operands, expr has different structure
        self.assertEqual(len(results), 0, "Different structure should not match")
        
    def test_match_symmetric_three_operands(self):
        """Test matching with exactly 3 operands"""
        # Pattern: $$var1 ~ $$var2 ~ $$var3
        pattern: kurt.Expr = [self.token_tilde, self.var1, self.var2, self.token_c]
        
        # Expression: a ~ b ~ c  
        expr: kurt.Expr = [self.token_tilde, self.token_a, self.token_b, self.token_c]
        
        subst = {}
        blocked = frozenset()
        unify_flag = False
        
        results = list(kurt.match_exprs_to_patterns(
            [(expr, pattern)], subst, blocked, unify_flag, self.kb))
        
        # Should find multiple permutations due to symmetry
        self.assertGreaterEqual(len(results), 1)
        
        # Collect all possible assignments for var1 and var2
        var1_assignments = set()
        var2_assignments = set()
        for r in results:
            if '$$var1' in r:
                assert isinstance(r['$$var1'], kurt.Token)
                var1_assignments.add(r['$$var1'].value if hasattr(r['$$var1'], 'value') else str(r['$$var1']))
            if '$$var2' in r:
                assert isinstance(r['$$var2'], kurt.Token)
                var2_assignments.add(r['$$var2'].value if hasattr(r['$$var2'], 'value') else str(r['$$var2']))
        
        # Due to symmetry, we should see permutations
        self.assertGreaterEqual(len(var1_assignments), 2, "Should see multiple values for $$var1 due to symmetry")
        
    def test_compare_with_flat_symmetric(self):
        """Compare behavior with flat symmetric operator"""
        # Create a flat symmetric operator for comparison
        kb_flat = kurt.KnowledgeBase()
        kb_flat.add_infix('&', 15, 15)
        kb_flat.add_sym('&')
        kb_flat.add_flat('&')
        
        token_amp = kurt.Token('SYMBOL', '&')
        
        # Non-flat: a ~ b ~ c (structure: [~, a, b, c])
        expr_nonflat: kurt.Expr = [self.token_tilde, self.token_a, self.token_b, self.token_c]
        pattern_nonflat: kurt.Expr = [self.token_tilde, self.var1, self.var2]

        # Flat: a & b & c (structure: [&, a, b, c])
        expr_flat: kurt.Expr = [token_amp, self.token_a, self.token_b, self.token_c]
        pattern_flat: kurt.Expr = [token_amp, self.var1, self.var2]
        
        subst = {}
        blocked = frozenset()
        unify_flag = False
        
        # Non-flat matching (should fail - different lengths)
        results_nonflat = list(kurt.match_exprs_to_patterns(
            [(expr_nonflat, pattern_nonflat)], subst, blocked, unify_flag, self.kb))
        
        # Flat matching (should succeed - can split)
        results_flat = list(kurt.match_exprs_to_patterns(
            [(expr_flat, pattern_flat)], subst, blocked, unify_flag, kb_flat))
        
        # Non-flat should fail due to length mismatch
        self.assertEqual(len(results_nonflat), 0, "Non-flat should reject different lengths")
        
        # Flat should succeed due to splitting capability
        self.assertGreater(len(results_flat), 0, "Flat should allow splitting")
        
    def test_nested_symmetric_expressions(self):
        """Test matching nested symmetric expressions"""
        # Pattern: ($$var1 ~ $$var2) ~ c
        inner_pattern: kurt.Expr = [self.token_tilde, self.var1, self.var2]
        pattern: kurt.Expr = [self.token_tilde, inner_pattern, self.token_c]
        
        # Expression: (a ~ b) ~ c
        inner_expr: kurt.Expr = [self.token_tilde, self.token_a, self.token_b]
        expr: kurt.Expr = [self.token_tilde, inner_expr, self.token_c]
        
        subst = {}
        blocked = frozenset()
        unify_flag = False
        
        results = list(kurt.match_exprs_to_patterns(
            [(expr, pattern)], subst, blocked, unify_flag, self.kb))
        
        self.assertGreater(len(results), 0, "Should match nested symmetric expressions")
        
        # Check that the inner pattern matched correctly
        found_correct = any(
            r.get('$$var1') == self.token_a and r.get('$$var2') == self.token_b
            for r in results
        )
        self.assertTrue(found_correct, "Should correctly match inner variables")

if __name__ == '__main__':
    unittest.main()