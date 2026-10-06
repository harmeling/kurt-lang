import contextlib
import copy
import io
import unittest

import kurt.kurt as kurt


M = [('[', ']')]          # a pair bound to `matrix`


class TestRowsByLine(unittest.TestCase):
    # a statement over several lines: line breaks are spaces, except in a bracket pair bound to
    # `matrix` (matrix.kurt's `calc [ matrix`) without another one inside: there each line is a row

    def test_rows(self):
        self.assertEqual(kurt.rows_by_line('A = [1, 2, 3\n     4, 5, 6]', M), 'A = [[1, 2, 3], [4, 5, 6]]')
        self.assertEqual(kurt.rows_by_line('[1\n0\n1]', M), '[[1], [0], [1]]')
        self.assertEqual(kurt.rows_by_line('[1, 2,   ; a comment\n 3, 4]', M), '[[1, 2], [3, 4]]')

    def test_other_line_breaks_are_spaces(self):
        self.assertEqual(kurt.rows_by_line('f(a,\n  b)', M), 'f(a,   b)')
        self.assertEqual(kurt.rows_by_line('[[1, 2],\n [3, 4]]', M), '[[1, 2],  [3, 4]]')    # nested: as written
        self.assertEqual(kurt.rows_by_line('a = [1,\n', M), 'a = [1, ')                     # not closed yet
        self.assertEqual(kurt.rows_by_line('[1, 2]', M), '[1, 2]')


    def test_only_brackets_bound_to_matrix(self):
        self.assertEqual(kurt.rows_by_line('[1, 2\n3, 4]', []), '[1, 2 3, 4]')            # no binding: a space
        self.assertEqual(kurt.rows_by_line('⟨1, 2\n3, 4⟩', [('⟨', '⟩')]), '⟨⟨1, 2⟩, ⟨3, 4⟩⟩')   # another pair bound
        kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kb = kurt.load_file('matrix', kb)
        self.assertEqual(kurt.matrix_brackets(kb), [('[', ']')])
        self.assertEqual(kurt.matrix_brackets(copy.deepcopy(kurt.initial_kb)), [])


class TestMatrixValues(unittest.TestCase):
    def test_determinant_and_product(self):
        F = kurt.Fraction
        self.assertEqual(kurt.determinant([[F(1), F(2)], [F(3), F(4)]]), -2)
        self.assertEqual(kurt.determinant([[F(0), F(1)], [F(1), F(0)]]), -1)    # a row swap
        self.assertIsNone(kurt.determinant([[F(1), F(2)]]))                       # not square
        self.assertEqual(kurt.matrix_product([[F(1), F(2)]], [[F(3)], [F(4)]]), [[11]])
        self.assertIsNone(kurt.matrix_product([[F(1), F(2)]], [[F(3), F(4)]]))    # the shapes don't fit


if __name__ == '__main__':
    unittest.main()
