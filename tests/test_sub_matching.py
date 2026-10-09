import copy
import random
import unittest

import kurt.kurt as kurt
from tests.utils import with_quantifiers

# Matching a formula `G` against the pattern `sub $x $a %A` means finding `$a` and `%A` with
# `G == %A[$x := $a]` (up to flattening/sorting and alpha-equivalence) -- second-order matching,
# which kurt does by enumerating candidates. These tests check that
#   - every solution really gives `G` back (soundness), and
#   - the solutions include the ones they should (completeness, for what kurt supports).
# Most are random round trips: build `A` with holes `$x`, pick `a`, compute `G = A[$x := a]`,
# and match `G` against `sub $x $a %A`.


def make_kb() -> kurt.KnowledgeBase:
    kb = with_quantifiers(copy.deepcopy(kurt.initial_kb))
    kb = kb.push_level('sandbox', [])
    for s in ['P', 'Q', 'R']:
        kb.add_bool(s, [0])
    kb.add_arity('P', 1)
    kb.add_arity('R', 2)
    kb.add_arity('f', 1)
    kb.add_arity('g', 2)
    kb.add_infix('plus', 60, 60)
    kb.add_flat('plus')
    kb.add_sym('plus')
    for s in ['P', 'Q', 'R', 'f', 'g', 'plus', 'c', 'd', 'e']:
        if not kb.is_const(s):
            kb.add_const(s)
    return kb


def parse(text: str, kb: kurt.KnowledgeBase) -> kurt.Expr:
    ts = kurt.PeekableGenerator(kurt.scan_string(text, kb))
    _, exprs, _, _ = kurt.parse_tokenstream(ts, kb)
    assert len(exprs) == 1
    return exprs[0]


def show(e, kb) -> str:
    return 'None' if e is None else kurt.expr_str(e, kb)


def value(pattern_part: kurt.Expr, s: kurt.State, kb) -> kurt.Expr:
    return kurt.apply_subst(pattern_part, s, kb)


def goal(A: kurt.Expr, x: str, a: kurt.Expr, kb) -> kurt.Expr:
    # `A[x := a]` as the engine sees a formula: bound variables renamed to fresh names
    return kurt.rename_all_vars(substitute(A, x, a, kb), kb)


def substitute(A: kurt.Expr, x: str, a: kurt.Expr, kb) -> kurt.Expr:
    # `A[x := a]`, capture-avoiding and normalized, via kurt's own `sub` evaluation
    sub = [kurt.Token('SYMBOL', kurt.SUB_SYMBOL), kurt.Token('SYMBOL', x), a, A]
    result, _ = kurt.trigger_sub(sub, kurt.State.empty(), kb)
    return result


def unbound(e: kurt.Expr, kb) -> bool:
    return isinstance(e, kurt.Token) and isinstance(e.value, str) and kb.is_var(e.value)


def solutions(G: kurt.Expr, pattern: kurt.Expr, kb, s: kurt.State | None = None) -> list[kurt.State]:
    return list(kurt.unify_exprs_with_patterns([(G, pattern)], s or kurt.State.empty(), kb))


# random formulas: `A` may contain the holes `$x` (and `$y`), and bound variables `u`, `v`
class Generator:
    def __init__(self, seed: int, holes: tuple[str, ...] = ('$x',)):
        self.rnd = random.Random(seed)
        self.holes = holes

    def term(self, depth: int, bound: list[str], holes: bool = True) -> str:
        r = self.rnd.random()
        leaves = ['c', 'd', 'e'] + bound + (list(self.holes) * 2 if holes else [])
        if depth <= 0 or r < 0.4:
            return self.rnd.choice(leaves)
        if r < 0.6:
            return f'(f {self.term(depth - 1, bound, holes)})'
        if r < 0.8:
            return f'(g {self.term(depth - 1, bound, holes)} {self.term(depth - 1, bound, holes)})'
        args = [self.term(depth - 1, bound, holes) for _ in range(self.rnd.randint(2, 3))]
        return '(' + ' plus '.join(args) + ')'

    def formula(self, depth: int, bound: list[str]) -> str:
        r = self.rnd.random()
        if depth <= 0 or r < 0.35:
            k = self.rnd.random()
            if k < 0.1:
                return 'Q'
            if k < 0.55:
                return f'(P {self.term(2, bound)})'
            return f'(R {self.term(2, bound)} {self.term(2, bound)})'
        if r < 0.55:
            return f'({self.formula(depth - 1, bound)} and {self.formula(depth - 1, bound)})'
        if r < 0.75:
            return f'({self.formula(depth - 1, bound)} implies {self.formula(depth - 1, bound)})'
        v = self.rnd.choice(['u', 'v'])
        return f'(forall {v} {self.formula(depth - 1, bound + [v])})'

    def value(self) -> str:
        return self.term(2, [], holes=False)


class TestSubMatchingRoundTrip(unittest.TestCase):
    TRIALS = 60

    def setUp(self):
        self.kb = make_kb()

    def check_sound(self, G, pattern_parts, sols, kb):
        # every solution must give `G` back
        x, p_a, p_A = pattern_parts
        for s in sols:
            a = value(p_a, s, kb)
            A = value(p_A, s, kb)
            if unbound(a, kb):
                a = kurt.Token('SYMBOL', 'zzz')     # unconstrained: `A` must not mention `$x`
            self.assertTrue(kurt.equal_expr(substitute(A, x, a, kb), G, kb),
                            f'unsound: {show(G, kb)} is not {show(A, kb)} with {x} := {show(a, kb)}')

    def test_round_trip(self):
        kb = self.kb
        gen = Generator(seed=1)
        pattern = parse('sub $x $a %A', kb)
        for trial in range(self.TRIALS):
            A = parse(gen.formula(3, []), kb)
            a = parse(gen.value(), kb)
            G = goal(A, '$x', a, kb)
            with self.subTest(trial=trial, G=show(G, kb), A=show(A, kb), a=show(a, kb)):
                sols = solutions(G, pattern, kb)
                self.check_sound(G, ('$x', pattern[2], pattern[3]), sols, kb)
                if kurt.contains_symbol(A, '$x'):
                    found = [s for s in sols if kurt.equal_expr(value(pattern[2], s, kb), a, kb)]
                    self.assertTrue(len(found) > 0, f'no solution with $a = {show(a, kb)}')

    def test_round_trip_with_known_value(self):
        # `$a` already bound, e.g. by the equation in "equal-elim"
        kb = self.kb
        gen = Generator(seed=2)
        pattern = parse('sub $x $a %A', kb)
        for trial in range(self.TRIALS):
            A = parse(gen.formula(3, []), kb)
            a = parse(gen.value(), kb)
            G = goal(A, '$x', a, kb)
            with self.subTest(trial=trial, G=show(G, kb), a=show(a, kb)):
                s0 = kurt.State.empty().bind('$a', a)
                sols = solutions(G, pattern, kb, s0)
                self.check_sound(G, ('$x', pattern[2], pattern[3]), sols, kb)
                self.assertTrue(len(sols) > 0, 'no solution')

    def test_round_trip_with_known_body(self):
        # `%A` already bound, e.g. by the conclusion of "forall-elim"
        kb = self.kb
        gen = Generator(seed=3)
        pattern = parse('sub $x $a %A', kb)
        for trial in range(self.TRIALS):
            A = parse(gen.formula(3, []), kb)
            a = parse(gen.value(), kb)
            G = goal(A, '$x', a, kb)
            with self.subTest(trial=trial, G=show(G, kb), A=show(A, kb), a=show(a, kb)):
                s0 = kurt.State.empty().bind('%A', A)
                sols = solutions(G, pattern, kb, s0)
                self.check_sound(G, ('$x', pattern[2], pattern[3]), sols, kb)
                self.assertTrue(len(sols) > 0, 'no solution')
                if kurt.contains_symbol(A, '$x'):
                    self.assertTrue(any(kurt.equal_expr(value(pattern[2], s, kb), a, kb) for s in sols),
                                    f'no solution with $a = {show(a, kb)}')

    def test_nested_sub_is_rejected(self):
        # a rule about two variables is applied twice instead, one variable at a time
        for text in ['use (forall $x (forall $y %A)) implies sub $x $a (sub $y $b %A)',
                     'use (forall $x %A) implies sub $x (sub $y c (f $y)) %A']:
            with self.subTest(text=text):
                lexer_state = kurt.LexerState()
                with self.assertRaises(kurt.KurtException):
                    kurt.scan_parse_check_eval(text, lexer_state, self.kb, 1, '<test>')


class TestSubMatchingCases(unittest.TestCase):
    # exact expected solutions `($a, %A)` for small cases; `None` for an unconstrained `$a`
    CASES = [
        ('P c', 'sub $x $a %A', {('c', 'P $x'), ('None', 'P c')}),
        ('R c c', 'sub $x c %A', {('c', 'R $x c'), ('c', 'R c $x'), ('c', 'R $x $x'), ('c', 'R c c')}),
        ('P (c plus d plus e)', 'sub $x (d plus e) %A', {('d plus e', 'P (c plus $x)'), ('d plus e', 'P (c plus d plus e)')}),
        ('forall u (P u)', 'sub $x $a %A', {('None', 'forall u (P u)')}),     # never the bound `u`
        ('R c d', 'sub $x c (R $x d)', {('c', 'R $x d')}),
        ('R c d', 'sub $x $a (R $x d)', {('c', 'R $x d')}),
    ]

    def test_cases(self):
        kb = make_kb()
        for G_text, pattern_text, expected in self.CASES:
            G = parse(G_text, kb)
            pattern = parse(pattern_text, kb)
            with self.subTest(G=G_text, pattern=pattern_text):
                got = set()
                for s in solutions(G, pattern, kb):
                    a = value(pattern[2], s, kb)
                    A = value(pattern[3], s, kb)
                    got.add(('None' if unbound(a, kb) else show(a, kb), show(A, kb)))
                expected_norm = {(a if a == 'None' else show(parse(a, kb), kb), show(parse(A, kb), kb)) for a, A in expected}
                # every expected solution must be there, and every solution must be sound
                self.assertTrue(expected_norm <= got, f'missing {expected_norm - got}, got {got}')


if __name__ == '__main__':
    unittest.main()
