import copy
import contextlib
import io
import random
import sys
import unittest
from pathlib import Path

import kurt.kurt as kurt

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'scripts'))
import oracle_sorts  # noqa: E402  (scripts/oracle_sorts.py, the semantic oracle of the sorts)


def instance_valid(text: str, label: str, models: int = 200) -> bool:
    # the formula labelled `label` of `text`, checked in `models` random models (`valid_in`)
    kb = copy.deepcopy(kurt.initial_kb)
    import tempfile, os
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'oracle-test.kurt')
        Path(path).write_text(text, encoding='utf-8')
        with contextlib.redirect_stdout(io.StringIO()):
            kurt.load_file(path, kb)
    formula = next(f for f in kb.all_theory() if f.label == label)
    rng = random.Random(1)
    arithmetic = oracle_sorts.arithmetic_of(formula.expr, kb)
    for _ in range(models):
        m = oracle_sorts.Model(kb, rng, rng.randint(1, 3), arithmetic)
        if not oracle_sorts.valid_in(formula.expr, m, kb):
            return False
    return True


class TestOracleSorts(unittest.TestCase):
    HEAD = 'load natural\nany x\nreal y\nconst S\n'

    def test_the_bad_instance_of_one_sort_per_use_is_falsified(self):
        # (the instance the kernel accepted before 0ff9399: `∃!` over `any` from uniqueness over `real`)
        text = self.HEAD + 'use ((∀ y (y ∈ S ⇒ y = 1)) ∧ 1 ∈ S) ⇒ ∃! x (x ∈ S)  "bad"\n'
        self.assertFalse(instance_valid(text, 'bad'))

    def test_a_valid_instance_is_not(self):
        text = self.HEAD + 'use ((∀ x (x ∈ S ⇒ x = 1)) ∧ 1 ∈ S) ⇒ ∃! x (x ∈ S)  "good"\n'
        self.assertTrue(instance_valid(text, 'good'))

    def test_restriction_is_valid_widening_of_a_forall_is_not(self):
        text = self.HEAD + 'prop P\narity P 1\nuse (∀ x (P x)) ⇒ ∀ y (P y)  "restrict"\nuse (∀ y (P y)) ⇒ ∀ x (P x)  "widen"\n'
        self.assertTrue(instance_valid(text, 'restrict'))
        self.assertFalse(instance_valid(text, 'widen'))

    def test_equal_mappings_have_equal_values(self):
        # `f c` of a mapping `f` (an object, no `arity`) is the application of its value: Leibniz's
        # law for it holds in every model (before, the oracle read `f` at the head as an operator of
        # its own and refuted "equal-elim" in proofs/set-theory/function-extensionality.kurt)
        text = 'load set\nset f, g\nconst c\nuse (f = g) ⇒ (f c = g c)  "leibniz"\n'
        self.assertTrue(instance_valid(text, 'leibniz'))

    def test_a_set_by_its_elements_is_a_set(self):
        # `{x}` is no object applied to `x` (as `f c` of a mapping is): its value is a set of the
        # model, so a binder over the sets reaches it (the instance of "forall-cond-elim" in
        # proofs/logic-encodings/second-order-leibniz.kurt, refuted by the oracle of f761f0e)
        text = 'load set\nconst x, A\nuse ((∀ X ∈ Pow(A) (x ∈ X)) ∧ {x} ∈ Pow(A)) ⇒ x ∈ {x}  "inst"\n'
        self.assertTrue(instance_valid(text, 'inst'))


class TestOracleArithmetic(unittest.TestCase):
    # with arithmetic (the calculator's `+`, `<`, `∈ Nat`): the numbers are the rationals
    HEAD = 'load natural\nreal n\n'

    def test_an_arithmetic_falsehood_is_refuted(self):
        text = self.HEAD + 'use 2 + 2 = 5  "wrong"\nuse (n < 2) ⇒ (n < 1)  "wrong-order"\nuse -1 ∈ Nat  "wrong-set"\n'
        for label in ('wrong', 'wrong-order', 'wrong-set'):
            self.assertFalse(instance_valid(text, label), label)

    def test_an_arithmetic_truth_is_not(self):
        text = self.HEAD + 'use 2 + 2 = 4  "right"\nuse (n < 1) ⇒ (n < 2)  "right-order"\nuse 3 ∈ Nat  "right-set"\n'
        for label in ('right', 'right-order', 'right-set'):
            self.assertTrue(instance_valid(text, label), label)


if __name__ == '__main__':
    unittest.main()
