import unittest

import kurt.kurt as kurt

# `var real x, y, z` and `const real x, y, z`: the sort in front of the names, for each of them --
# `var x, y, z` and `real x, y, z` (plan step 3 of dev/todo.md)


def sorted_as(text: str, *names: str) -> bool:
    result = kurt.check_text('load number\n' + text + '\nreal\n')
    return result.ok and all(f'real {name} 0' in result.output for name in names)


class TestDeclarationSugar(unittest.TestCase):
    def test_var_with_a_sort(self):
        self.assertTrue(sorted_as('var real x, y, z', 'x', 'y', 'z'))

    def test_const_with_a_sort(self):
        self.assertTrue(sorted_as('const real c, d', 'c', 'd'))

    def test_the_names_are_variables_and_constants(self):
        result = kurt.check_text('load number\nvar real x, y\nconst real c\nuse x + 0 = x\nc + 0 = c\n')
        self.assertTrue(result.ok, result.error)

    def test_one_name(self):
        self.assertTrue(sorted_as('var real x', 'x'))

    def test_a_sort_with_a_position_is_not_the_sugar(self):
        result = kurt.check_text('load number\nvar real x 0\n')
        self.assertFalse(result.ok)

    def test_the_plain_form_still_works(self):
        result = kurt.check_text('load number\nvar x, y\nuse x + 0 = x\n')
        self.assertTrue(result.ok, result.error)


class TestSeveralBoundVariables(unittest.TestCase):
    # `∃ x, y, z P` is `∃ x ∃ y ∃ z P` (plan step 4)
    def test_exists_with_a_list_is_nested(self):
        a = kurt.check_text('load logic, number\nuse exists x, y (x < y) "two"\nexists a exists b (a < b)\n')
        self.assertTrue(a.ok, a.error)

    def test_forall_with_a_list(self):
        a = kurt.check_text('load logic, number\nuse forall x, y (x = y implies y = x) "sym"\nforall x forall y (x = y implies y = x)\n')
        self.assertTrue(a.ok, a.error)

    def test_a_condition_after_a_list_is_refused(self):
        a = kurt.check_text('load logic, number\nshow exists x, y > 0 (x < y)\n')
        self.assertEqual(a.error_kind, 'ParseError')

    def test_each_name_with_its_condition(self):
        a = kurt.check_text('load logic, number\nuse forall x > 0, y > 0 (x + y > 0) "pos"\nforall a > 0 forall b > 0 (a + b > 0)\n')
        self.assertTrue(a.ok, a.error)
