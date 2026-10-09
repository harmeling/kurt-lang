import contextlib
import copy
import io
import unittest

import kurt.kurt as kurt


M = [('[', ']')]          # a pair bound to `matrix`


class TestRowsByLine(unittest.TestCase):
    # a statement over several lines: line breaks are spaces, except in a bracket pair bound to
    # `matrix` (matrix.kurt's `builtin [ matrix`) without another one inside: there each line is a row

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


class TestMatrixDisplay(unittest.TestCase):
    def test_normal_output_aligns_matrix_rows_and_keeps_events_multiline(self):
        result = kurt.check_text(
            'load matrix\n'
            'use [[1, 20], [300, 4]] = [[1, 20], [300, 4]]\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('use [[  1, 20],', result.output)
        self.assertIn('     [300,  4]] = [[  1, 20],', result.output)
        self.assertNotIn('const ,', result.output)
        assumed = next(event for event in result.events if event['kind'] == 'assumed')
        self.assertIn('\n', assumed['text'])

    def test_row_vectors_and_sexpr_stay_on_one_line(self):
        row = kurt.check_text('load matrix\nuse [1, 2, 3] = [1, 2, 3]\n')
        tree = kurt.check_text(
            'load matrix\nformat sexpr\n'
            'use [[1, 2], [3, 4]] = [[1, 2], [3, 4]]\n'
        )
        self.assertTrue(row.ok, row.error)
        self.assertIn('use [1, 2, 3] = [1, 2, 3]', row.output)
        self.assertTrue(tree.ok, tree.error)
        assumed = next(event for event in tree.events if event['kind'] == 'assumed')
        self.assertNotIn('\n', assumed['text'])


if __name__ == '__main__':
    unittest.main()
