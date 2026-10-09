import contextlib
import copy
import io
import itertools
import os
import unittest

import kurt.kurt as kurt


class TestPropositionalSemantics(unittest.TestCase):
    """Check prop.kurt independently of Kurt's search and certificate kernel."""

    CONNECTIVES = {'true', 'false', 'not', 'and', 'or', 'implies', 'invimplies', 'iff'}

    def variables(self, expr):
        if isinstance(expr, kurt.Token):
            value = expr.value
            return {value} if isinstance(value, str) and value not in self.CONNECTIVES else set()
        found = set()
        for child in expr:
            found |= self.variables(child)
        return found

    def evaluate(self, expr, values):
        if isinstance(expr, kurt.Token):
            if expr.value == 'true':
                return True
            if expr.value == 'false':
                return False
            return values[expr.value]
        op, *args = expr
        name = op.value
        evaluated = [self.evaluate(arg, values) for arg in args]
        if name == 'not':
            return not evaluated[0]
        if name == 'and':
            return all(evaluated)
        if name == 'or':
            return any(evaluated)
        if name == 'implies':
            return not evaluated[0] or evaluated[1]
        if name == 'invimplies':
            return not evaluated[1] or evaluated[0]
        if name in ('iff', '='):
            return evaluated[0] == evaluated[1]
        raise ValueError(name)

    def test_every_pure_propositional_rule_and_theorem_is_a_tautology(self):
        kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kb = kurt.load_file('prop', kb)

        checked = []
        for formula in kb.all_theory():
            if os.path.basename(formula.filename) != 'prop.kurt':
                continue
            symbols = {token.value for token in kurt.get_token_set(formula.expr)}
            if 'sub' in symbols:
                continue  # `iff-subst` is a meta-level substitution rule, not a truth formula.
            unknown_operators = {formula.expr[0].value} - self.CONNECTIVES if isinstance(formula.expr, list) else set()
            self.assertFalse(unknown_operators, formula.formula_str(kb))
            variables = sorted(self.variables(formula.expr))
            for bits in itertools.product((False, True), repeat=len(variables)):
                valuation = dict(zip(variables, bits))
                self.assertTrue(self.evaluate(formula.expr, valuation),
                                (formula.label, formula.formula_str(kb), valuation))
            checked.append(formula.label)

        self.assertEqual(set(checked), {
            'and-intro', 'and-elim', 'or-intro', 'or-elim', 'or-elim-3', 'or-elim-4',
            'invimplies-def', 'iff-intro', 'iff-elim-forward', 'iff-elim-backward',
            'iff-reflexive', 'top-elim', 'iff-true-elim', 'iff-true-intro', 'bottom-intro',
            'bottom-elim', 'not-intro', 'not-elim', 'not-not-intro', 'not-not',
            'excluded-middle',
        })


if __name__ == '__main__':
    unittest.main()
