import contextlib
import copy
import io
import itertools
import random
import unittest

import kurt.kurt as kurt
from kurt.kurt import Token

# the kernel's own alpha-equivalence and substitution (`k_equal`, `k_replace`) against the search's
# (`equal_expr`, `capture_avoiding_replace`), on small generated terms with binders, a `sym`
# operator and shadowing -- a bounded, deterministic generator, no extra library


S = lambda v: Token('SYMBOL', v)


class TestKernelDifferential(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            self.kb = kurt.load_file('set', self.kb)
        for c in ('a', 'b', 'P', 'R'):
            self.kb.add_const(c)
        self.kb.add_arity('P', 1)
        self.kb.add_arity('R', 2)

    def terms(self, rng: random.Random, depth: int, bound: list[str]):
        # a random term: a constant, a bound or free variable, `P t`, `R t u`, `t = u` (sym), or a
        # binder (∀/∃ over `$x`/`$y`/`$z`, which can shadow)
        choices = ['const', 'var']
        if depth > 0:
            choices += ['P', 'R', 'eq', 'bind', 'bind']
        kind = rng.choice(choices)
        if kind == 'const':
            return S(rng.choice(['a', 'b']))
        if kind == 'var':
            return S(rng.choice(bound + ['$x', '$y', '$z']) if bound else rng.choice(['$x', '$y', '$z']))
        if kind == 'P':
            return [S('P'), self.terms(rng, depth - 1, bound)]
        if kind == 'R':
            return [S('R'), self.terms(rng, depth - 1, bound), self.terms(rng, depth - 1, bound)]
        if kind == 'eq':
            return [S('='), self.terms(rng, depth - 1, bound), self.terms(rng, depth - 1, bound)]
        v = rng.choice(['$x', '$y', '$z'])
        return [S(rng.choice(['forall', 'exists'])), S(v), self.terms(rng, depth - 1, bound + [v])]

    def rename_bound(self, e, rng: random.Random):
        # an alpha-variant: each binder's variable renamed to a fresh name
        if isinstance(e, Token):
            return e
        if isinstance(e[0], Token) and e[0].value in ('forall', 'exists'):
            old, new = e[1].value, f'$$d{rng.randrange(10**6)}'
            return [e[0], S(new), self.rename_bound(kurt.k_rename(e[2], old, new), rng)]
        return [self.rename_bound(c, rng) for c in e]

    def test_alpha_equivalence(self):
        rng = random.Random(1)
        for _ in range(300):
            t = self.terms(rng, 3, [])
            u = self.terms(rng, 3, [])
            variant = self.rename_bound(t, rng)
            self.assertTrue(kurt.k_equal(t, variant, self.kb), kurt.expr_str(t, self.kb))
            self.assertEqual(kurt.k_equal(t, u, self.kb), kurt.equal_expr(t, u, self.kb, keep_order=False),
                             (kurt.expr_str(t, self.kb), kurt.expr_str(u, self.kb)))

    def test_substitution(self):
        rng = random.Random(2)
        for _ in range(300):
            A = self.terms(rng, 3, [])
            t = self.terms(rng, 1, [])
            x = rng.choice(['$x', '$y', '$z'])
            if x in kurt.k_free(t, self.kb):
                continue                 # (the search never substitutes a term with the variable itself)
            kernel = kurt.k_replace(A, x, t, self.kb)
            search = kurt.capture_avoiding_replace(A, x, t, kurt.State.empty(), self.kb)
            self.assertTrue(kurt.k_equal(kernel, search, self.kb),
                            (kurt.expr_str(A, self.kb), x, kurt.expr_str(t, self.kb), kurt.expr_str(kernel, self.kb), kurt.expr_str(search, self.kb)))

if __name__ == '__main__':
    unittest.main()
