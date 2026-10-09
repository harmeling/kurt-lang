import contextlib
import copy
import io
import itertools
import math
import os
import unittest
from fractions import Fraction

import kurt.kurt as kurt


class UndefinedArithmetic(Exception):
    pass


class TestNumberTheorySemantics(unittest.TestCase):
    """Search for finite rational counterexamples to every axiom in numbers.kurt."""

    def evaluate(self, expr, values):
        if isinstance(expr, kurt.Token):
            if expr.label in ('INT', 'FLOAT'):
                return Fraction(expr.value)
            if expr.value == 'true':
                return True
            if expr.value == 'false':
                return False
            if isinstance(expr.value, str) and expr.value.startswith('$'):
                return values[expr.value]
            raise UndefinedArithmetic(expr.value)

        op = expr[0].value
        # Short circuit implication/conjunction/disjunction. Besides matching their semantics,
        # this avoids evaluating an undefined consequent such as (-1)! when its guard is false.
        if op == 'implies':
            return not self.evaluate(expr[1], values) or self.evaluate(expr[2], values)
        if op == 'and':
            return all(self.evaluate(arg, values) for arg in expr[1:])
        if op == 'or':
            return any(self.evaluate(arg, values) for arg in expr[1:])
        if op == 'not':
            return not self.evaluate(expr[1], values)

        args = [self.evaluate(arg, values) for arg in expr[1:]]
        if op in ('iff', '='):
            return args[0] == args[1]
        if op == '≠':
            return args[0] != args[1]
        if op == '+':
            return sum(args, Fraction())
        if op == '-':
            return -args[0] if len(args) == 1 else args[0] - args[1]
        if op == '*':
            return math.prod(args)
        if op == '/':
            if args[1] == 0:
                raise UndefinedArithmetic('division by zero')
            return args[0] / args[1]
        if op == '^':
            if args[1].denominator != 1 or (args[0] == 0 and args[1] < 0):
                raise UndefinedArithmetic('power outside sampled rational interpretation')
            return args[0] ** int(args[1])
        if op == '!':
            if args[0].denominator != 1 or args[0] < 0:
                raise UndefinedArithmetic('factorial outside nonnegative integers')
            return Fraction(math.factorial(int(args[0])))
        if op in ('<', '>', '<=', '>='):
            return {'<': args[0] < args[1], '>': args[0] > args[1],
                    '<=': args[0] <= args[1], '>=': args[0] >= args[1]}[op]
        raise UndefinedArithmetic(op)

    def test_all_number_axioms_on_small_exact_values(self):
        kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kb = kurt.load_file('numbers', kb)

        domain = tuple(Fraction(n) for n in (-2, -1, 0, 1, 2))
        checked = []
        for formula in kb.all_theory():
            if os.path.basename(formula.filename) != 'numbers.kurt':
                continue
            variables = sorted({token.value for token in kurt.get_token_set(formula.expr)
                                if isinstance(token.value, str) and token.value.startswith('$')})
            defined_cases = 0
            for sample in itertools.product(domain, repeat=len(variables)):
                valuation = dict(zip(variables, sample))
                try:
                    result = self.evaluate(formula.expr, valuation)
                except UndefinedArithmetic:
                    continue
                defined_cases += 1
                self.assertTrue(result, (formula.label, formula.formula_str(kb), valuation))
            self.assertGreater(defined_cases, 0, formula.label)
            checked.append(formula.label)

        self.assertEqual(len(checked), 76)


if __name__ == '__main__':
    unittest.main()
