import unittest
from kurt import *

class TestMatchExpr(unittest.TestCase):
    def setUp(self):
        """Set up a mock KnowledgeBase with basic functionality"""
        class MockKB:
            def is_var(self, value):
                return value.startswith('$')  # Variables start with $

        self.kb = MockKB()

    def test_symbol_matching(self):
        """Test exact symbol matching"""
        expr = Token(label='SYMBOL', value='a')
        pattern = Token(label='SYMBOL', value='a')
        exprs_patterns = [(expr, pattern)]
        subst = {}

        matches = list(match_expr(exprs_patterns, subst, self.kb))
        self.assertEqual(matches, [{}])  # No substitution needed

    def test_variable_matching(self):
        """Test matching a variable to a symbol"""
        expr = Token(label='SYMBOL', value='hello')
        pattern = Token(label='SYMBOL', value='$x')
        exprs_patterns = [(expr, pattern)]
        subst = {}

        matches = list(match_expr(exprs_patterns, subst, self.kb))
        self.assertEqual(matches, [{'$x': Token(label='SYMBOL', value='hello')}])

    def test_list_matching(self):
        """Test matching lists with variables"""
        expr = [Token(label='SYMBOL', value='f'), Token(label='SYMBOL', value='x')]
        pattern = [Token(label='SYMBOL', value='f'), Token(label='SYMBOL', value='$y')]
        exprs_patterns = [(expr, pattern)]
        subst = {}

        matches = list(match_expr(exprs_patterns, subst, self.kb))
        self.assertEqual(matches, [{'$y': Token(label='SYMBOL', value='x')}])

    def test_nested_list_matching(self):
        """Test matching nested lists"""
        expr = [Token(label='SYMBOL', value='f'), 
                [Token(label='SYMBOL', value='a'), Token(label='SYMBOL', value='b')]]
        pattern = [Token(label='SYMBOL', value='f'), 
                   [Token(label='SYMBOL', value='$x'), Token(label='SYMBOL', value='$y')]]
        exprs_patterns = [(expr, pattern)]
        subst = {}

        matches = list(match_expr(exprs_patterns, subst, self.kb))
        self.assertEqual(matches, [{'$x': Token(label='SYMBOL', value='a'), '$y': Token(label='SYMBOL', value='b')}])

    def test_sub_rule_basic(self):
        """Test basic substitution rule: sub $x $a $A"""
        expr = [Token(label='SYMBOL', value='f'), Token(label='SYMBOL', value='hello')]
        pattern = [Token(label='SYMBOL', value='f'),
                   [Token(label='SYMBOL', value='sub'),
                    Token(label='SYMBOL', value='$x'),
                    Token(label='SYMBOL', value='hello'),
                    Token(label='SYMBOL', value='$x')]]
        exprs_patterns = [(expr, pattern)]
        subst = {}

        matches = list(match_expr(exprs_patterns, subst, self.kb))
        self.assertEqual(matches, [{'$x': Token(label='SYMBOL', value='hello')}])

    def test_sub_rule_nested(self):
        """Test substitution rule with nested structures"""
        expr = [Token(label='SYMBOL', value='g'), 
                [Token(label='SYMBOL', value='world')]]
        pattern = [Token(label='SYMBOL', value='g'),
                   [Token(label='SYMBOL', value='sub'),
                    Token(label='SYMBOL', value='$y'),
                    Token(label='SYMBOL', value='world'),
                    [Token(label='SYMBOL', value='$y')]]]
        exprs_patterns = [(expr, pattern)]
        subst = {}

        matches = list(match_expr(exprs_patterns, subst, self.kb))
        self.assertEqual(matches, [{'$y': Token(label='SYMBOL', value='world')}])

if __name__ == '__main__':
    unittest.main()