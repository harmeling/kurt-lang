import unittest

class TestApplySubst(unittest.TestCase):
    def setUp(self):
        """Set up a mock KnowledgeBase with basic functionality"""
        class MockKB:
            def is_var(self, value):
                return value.startswith('$')  # Variables start with $

        self.kb = MockKB()

    def test_apply_subst_basic(self):
        """Test basic substitution of a variable"""
        expr = Token(label='SYMBOL', value='$x')
        subst = {'$x': Token(label='SYMBOL', value='hello')}

        result = apply_subst(expr, subst, self.kb)
        self.assertEqual(result, Token(label='SYMBOL', value='hello'))

    def test_apply_subst_no_substitution(self):
        """Test when no substitution occurs"""
        expr = Token(label='SYMBOL', value='hello')
        subst = {'$x': Token(label='SYMBOL', value='world')}  # No match

        result = apply_subst(expr, subst, self.kb)
        self.assertEqual(result, expr)  # Should remain unchanged

    def test_apply_subst_list(self):
        """Test substitution inside a list"""
        expr = [Token(label='SYMBOL', value='$x'), Token(label='SYMBOL', value='$y')]
        subst = {'$x': Token(label='SYMBOL', value='a'), '$y': Token(label='SYMBOL', value='b')}

        result = apply_subst(expr, subst, self.kb)
        expected = [Token(label='SYMBOL', value='a'), Token(label='SYMBOL', value='b')]

        self.assertEqual(result, expected)

    def test_apply_subst_nested_list(self):
        """Test substitution inside a nested list"""
        expr = [Token(label='SYMBOL', value='f'),
                [Token(label='SYMBOL', value='$x'), Token(label='SYMBOL', value='$y')]]
        subst = {'$x': Token(label='SYMBOL', value='1'), '$y': Token(label='SYMBOL', value='2')}

        result = apply_subst(expr, subst, self.kb)
        expected = [Token(label='SYMBOL', value='f'),
                    [Token(label='SYMBOL', value='1'), Token(label='SYMBOL', value='2')]]

        self.assertEqual(result, expected)

    def test_apply_subst_to_free_vars_bound_variable(self):
        """Test that bound variables are not substituted"""
        def mock_free_bound_vars(expr, kb):
            free_vars = {'$x'}
            bound_vars = {'$y'}
            return free_vars, bound_vars

        global free_bound_vars
        free_bound_vars = mock_free_bound_vars  # Mock function

        expr = [Token(label='SYMBOL', value='$x'), Token(label='SYMBOL', value='$y')]
        subst = {'$x': Token(label='SYMBOL', value='hello'), '$y': Token(label='SYMBOL', value='world')}

        result = apply_subst_to_free_vars(expr, subst, self.kb)
        expected = [Token(label='SYMBOL', value='hello'), Token(label='SYMBOL', value='$y')]  # $y remains unchanged

        self.assertEqual(result, expected)

if __name__ == '__main__':
    unittest.main()