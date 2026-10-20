"""Finite-model checks of the first-order theories, apart from Kurt's search and kernel.

The truth tables of tests/test_prop_semantics.py and the small-value checks of
tests/test_numbers_semantics.py don't reach the rules with quantifiers, `sub` and binders:
logic.kurt, equality.kurt and set.kurt. This file evaluates their statements in small finite
models -- a domain of a few elements, `∀`/`∃`/`∃!` by enumeration (also with a condition,
`∀ $x ∈ $A ...`), `=` as identity, `sub $x $a %A` by substitution -- and asserts that every
axiom (`use`, `def`) and every stated theorem (`show`) holds in *every* interpretation: all
assignments of its free `$`-variables, and all tables for its schema variables (`%A`). An
independent evaluator: it reads only the expression trees and never calls the search or
`kernel_verify`, so a rule that is wrong in the same way in both would still fail here.

The reading of a schema variable (doc/kurt-doc.md §4.4, "A schema variable in the body of a
binder"): `%A` stands for a formula, in a model a table over the variables it may depend on.
Those are the hole of every `sub $x _ %A` applied to it (`sub $x $a %A` is `%A` at `$a`), and
the variable of every binder in whose scope `%A` occurs directly -- but not a binder's variable
`$w` that an occurrence only reaches *through* a substitution `sub $x $w %A` of that variable:
that is the standard proviso "`$w` not free in `%A`" of such rules (`∀ $w (sub $x $w %C) ...`
in "forall-cond-def"; `%C` "never mentions the bound variable itself"). The free `$`-variables
of the statement aren't in the tables: for a fixed assignment of them, a formula is just some
predicate of the remaining variables, and the outer loop over the assignments covers every
such predicate. Each table is exhaustively enumerated, so the domain stays tiny where a schema
has two or three variables (2^(|D|^k) tables).

Sets (set.kurt): the domain is a transitive universe of hereditarily finite sets -- every
object is a set, as the theory assumes -- with `∈` as membership, pairs as Kuratowski pairs
`{{a}, {a, b}}` (so a pair is a set too, and extensionality holds of it), `A × B`, `Pow`,
`A → B` (the set of all mappings, as sets of pairs) and `{$z ∈ $A | %F}` computed as sets, and
`f a` as the unique `b` with `(a, b) ∈ f`. The universe is not closed under `Pow`, `×` and `→`
(no finite one is): a computed value may lie outside it, and `fst`/`snd` of a non-pair or the
application of a non-mapping is undefined -- such a sample is skipped, like 1/0 in
test_numbers_semantics.py, and the test asserts that every statement still has samples where
its antecedent holds (both sides of an `iff` take both values), so no check passes vacuously.

A statement that fails here is a finding about the theory, not about the oracle.
"""

import contextlib
import copy
import io
import itertools
import os
import unittest

import kurt.kurt as kurt


class Undefined(Exception):
    """A sample where a partial operation has no value (`fst ∅`, `f a` of a non-mapping)."""


class Unsupported(Exception):
    """A symbol the model doesn't interpret: the statement is skipped, with this reason."""


BINDERS = ('forall', 'exists', 'existsunique')
SETBUILDER = '|'


def token_name(e):
    return e.value if isinstance(e, kurt.Token) and isinstance(e.value, str) else None


def is_variable(name):
    return isinstance(name, str) and name[:1] in ('$', '%')


def binder_variable(first):
    """The variable a binder's first argument binds, and the condition on it (or None)."""
    if isinstance(first, kurt.Token):
        return token_name(first), None
    op = token_name(first[0])
    if op == kurt.BOUND_SYMBOL:                  # `[bound:, $c, $c ∈ $a]`, a condition as written
        return token_name(first[1]), first[2]
    if op == 'sub':                              # `sub $x $v %C`: a rule's binder with any condition
        return token_name(first[2]), first
    raise Unsupported(f'binder over `{op}`')


def term_variables(e):
    if isinstance(e, kurt.Token):
        return {e.value} if is_variable(e.value) else set()
    return set().union(*(term_variables(arg) for arg in e))


def analyse(expr):
    """The variables each schema variable's table ranges over, and the statement's free variables.

    Returns (deps, free, depth): `deps[%A]` is the ordered tuple of variables `%A` may depend on,
    `free` the `$`-variables that occur as values outside every binder on them (the outer loop
    assigns them), `depth` the deepest nesting of binders (for the cost estimate)."""
    allowed, forbidden, holes = {}, {}, {}
    free, depth = set(), [0]

    def walk(e, scope, subs):
        # scope: the variables bound by the enclosing binders; subs: (hole, variables of the term)
        # of the enclosing substitutions
        if isinstance(e, kurt.Token):
            v = token_name(e)
            if v is None or not is_variable(v):
                return
            if v.startswith('%'):
                holes.setdefault(v, set()).update(h for h, _ in subs)
                bad = {w for w in scope for h, tv in subs if w in tv and w != h}
                forbidden.setdefault(v, set()).update(bad)
                allowed.setdefault(v, set()).update(set(scope) - bad)
            elif v not in scope:
                free.add(v)
            return
        op = token_name(e[0])
        if op == 'sub':
            hole, term, body = e[1], e[2], e[3]
            walk(term, scope, subs)
            walk(body, scope, subs + ((token_name(hole), term_variables(term)),))
        elif op in BINDERS or op == SETBUILDER:
            v, condition = binder_variable(e[1])
            inner = scope + (v,)
            depth[0] = max(depth[0], len(inner))
            if condition is not None:
                walk(condition, inner, subs)
            for arg in e[2:]:
                walk(arg, inner, subs)
        else:
            for arg in e:
                walk(arg, scope, subs)

    walk(expr, (), ())
    deps = {v: tuple(sorted(holes[v] | (allowed[v] - forbidden[v]))) for v in allowed}
    return deps, tuple(sorted(free)), depth[0]


class Evaluator:
    """Evaluates an expression tree in a model, under tables for its schema variables.

    The connectives are three-valued only as far as a partial operation needs: `A ∧ B` is false
    when one side is false even if the other has no value, so a sample isn't lost to an
    undefined conjunct that doesn't matter (`f a` next to `f ∈ (A → B)` for a non-mapping `f`)."""

    def __init__(self, model, deps, tables):
        self.model = model
        self.deps = deps
        self.tables = tables

    def defined(self, e, env):
        try:
            return self.eval(e, env)
        except Undefined:
            return None

    def eval(self, e, env):
        if isinstance(e, kurt.Token):
            v = e.value
            if v == 'true':
                return True
            if v == 'false':
                return False
            if isinstance(v, str) and v.startswith('%'):
                if v in env:                     # a hole bound by `sub` (propositional.kurt's "iff-subst")
                    return env[v]
                return self.tables[v][tuple(env[d] for d in self.deps[v])]
            if isinstance(v, str) and v.startswith('$'):
                return env[v]
            return self.model.constant(e)
        head, args = e[0], e[1:]
        op = token_name(head)
        if op == 'not':
            return not self.eval(args[0], env)
        if op == 'and':
            values = [self.defined(arg, env) for arg in args]
            if False in values:
                return False
            if None in values:
                raise Undefined('and')
            return True
        if op == 'or':
            values = [self.defined(arg, env) for arg in args]
            if True in values:
                return True
            if None in values:
                raise Undefined('or')
            return False
        if op == 'implies':
            antecedent = self.defined(args[0], env)
            if antecedent is False:
                return True
            consequent = self.defined(args[1], env)
            if consequent is True:
                return True
            if antecedent is None or consequent is None:
                raise Undefined('implies')
            return False
        if op == 'iff':
            return self.eval(args[0], env) == self.eval(args[1], env)
        if op == '=':
            return self.eval(args[0], env) == self.eval(args[1], env)
        if op == 'sub':
            hole, term, body = args
            return self.eval(body, {**env, token_name(hole): self.eval(term, env)})
        if op in BINDERS or op == SETBUILDER:
            v, condition = binder_variable(args[0])
            body = args[1]
            instances = ({**env, v: d} for d in self.model.domain)
            if condition is not None:
                instances = (env2 for env2 in instances if self.eval(condition, env2))
            if op == 'forall':
                return all(self.eval(body, env2) for env2 in instances)
            if op == 'exists':
                return any(self.eval(body, env2) for env2 in instances)
            if op == 'existsunique':
                witnesses = (env2 for env2 in instances if self.eval(body, env2))
                return len(list(itertools.islice(witnesses, 2))) == 1
            return frozenset(env2[v] for env2 in instances if self.eval(body, env2))
        values = [self.eval(arg, env) for arg in args]
        if is_variable(op):                      # `$f $a`: the application of a value
            return self.model.apply(self.eval(head, env), values)
        return self.model.operation(op, values)


class PureModel:
    """A domain of `n` bare elements: `=` is identity, nothing else is interpreted."""

    def __init__(self, n):
        self.domain = tuple(range(n))
        self.name = f'{n} elements'

    def constant(self, token):
        raise Unsupported(f'constant `{token.value}`')

    def operation(self, op, values):
        raise Unsupported(f'operator `{op}`')

    def apply(self, function, values):
        raise Unsupported('application')


EMPTY = frozenset()


def pair(a, b):
    return frozenset({frozenset({a}), frozenset({a, b})})


def unpair(p):
    """The components of a Kuratowski pair; Undefined for a set that isn't one."""
    if not isinstance(p, frozenset) or not all(isinstance(s, frozenset) for s in p):
        raise Undefined('not a pair')
    singletons = [s for s in p if len(s) == 1]
    if len(p) == 1 and singletons:
        (a,) = singletons[0]
        return a, a
    if len(p) == 2 and len(singletons) == 1:
        (a,) = singletons[0]
        (other,) = [s for s in p if len(s) == 2]
        if a in other:
            (b,) = other - {a}
            return a, b
    raise Undefined('not a pair')


def transitive_closure(seeds):
    universe, todo = set(), list(seeds)
    while todo:
        s = todo.pop()
        if s not in universe:
            universe.add(s)
            todo.extend(s)
    return frozenset(universe)


def powerset(s):
    elements = list(s)
    return frozenset(frozenset(c) for r in range(len(elements) + 1)
                     for c in itertools.combinations(elements, r))


V2 = frozenset({EMPTY, frozenset({EMPTY})})                  # ∅, {∅}
V3 = powerset(V2)                                             # the 4 sets of rank ≤ 2
PAIRS_V2 = frozenset(pair(a, b) for a in V2 for b in V2)
# the universes, all transitive (closed under elements, so that extensionality holds in them):
# 5 sets, with the mapping `{(∅, ∅)}` = {{{∅}}} as an element; 10 sets, with every pair of ∅ and
# {∅} and the mappings of one pair; and 21 sets, with every set of such pairs (all mappings
# between subsets of {∅, {∅}})
UNIVERSE_5 = transitive_closure(V3 | {frozenset({pair(EMPTY, EMPTY)})})
UNIVERSE_10 = transitive_closure(V3 | PAIRS_V2 | {frozenset({p}) for p in PAIRS_V2})
UNIVERSE_21 = transitive_closure(V3 | powerset(PAIRS_V2))


class SetModel:
    """Hereditarily finite sets: membership, pairs, products, power sets and mappings computed."""

    def __init__(self, universe):
        def rank(s):
            return max((rank(t) for t in s), default=-1) + 1
        self.domain = tuple(sorted(universe, key=lambda s: (rank(s), len(s), sorted(map(repr, s)))))
        self.name = f'{len(self.domain)} sets'

    def constant(self, token):
        if token.value == '∅':
            return EMPTY
        raise Unsupported(f'constant `{token.value}`')

    def operation(self, op, values):
        if op == ',':
            return tuple(values)                 # a list, consumed by the brackets around it
        if op == '($$$)':                        # round brackets: a tuple, or just a value
            (x,) = values
            if isinstance(x, tuple):
                return self.tuple_of(x)
            return x
        if op == '{$$$}':                        # curly brackets: the set of the elements listed
            (x,) = values
            return frozenset(x if isinstance(x, tuple) else {x})
        if op == 'in':
            return values[0] in values[1]
        if op == '∪':
            return values[0] | values[1]
        if op == '∩':
            return values[0] & values[1]
        if op == '⊂':
            return values[0] <= values[1]
        if op == 'Pow':
            return powerset(values[0])
        if op == 'fst':
            return unpair(values[0])[0]
        if op == 'snd':
            return unpair(values[0])[1]
        if op == '×':
            return frozenset(pair(a, b) for a in values[0] for b in values[1])
        if op == '→':
            a_list, b_list = list(values[0]), list(values[1])
            return frozenset(frozenset(pair(a, b) for a, b in zip(a_list, image))
                             for image in itertools.product(b_list, repeat=len(a_list)))
        raise Unsupported(f'operator `{op}`')

    def tuple_of(self, components):
        if len(components) == 1:
            return components[0]
        return pair(components[0], self.tuple_of(components[1:]))

    def apply(self, function, values):
        (a,) = values
        if not isinstance(function, frozenset):
            raise Undefined('not a mapping')
        images = set()
        for p in function:
            try:
                x, y = unpair(p)
            except Undefined:
                continue
            if x == a:
                images.add(y)
        if len(images) != 1:
            raise Undefined('not a mapping defined here')
        return images.pop()


BOOLEANS = (False, True)
BUDGET = 60000          # the most samples (× tables) one statement is checked with per model


def table_domain(model, variable):
    return BOOLEANS if variable.startswith('%') else model.domain


def all_tables(model, deps):
    """Every interpretation of the schema variables: for each, a table over its variables."""
    names = sorted(deps)
    per_name = []
    for v in names:
        keys = list(itertools.product(*(table_domain(model, d) for d in deps[v])))
        per_name.append([dict(zip(keys, bits)) for bits in itertools.product(BOOLEANS, repeat=len(keys))])
    for choice in itertools.product(*per_name):
        yield dict(zip(names, choice))


def cost(model, deps, free, depth):
    """The number of samples × tables the check of a statement enumerates in `model`."""
    n = len(model.domain)
    tables = 1
    for v in deps:
        keys = 1
        for d in deps[v]:
            keys *= len(table_domain(model, d))
        tables *= 2 ** keys
    return tables * n ** (len(free) + depth)


class Check:
    """What one statement's check saw: the models it was checked in, and the informative samples."""

    def __init__(self, label):
        self.label = label
        self.models = []            # the models within the budget, smallest first
        self.samples = 0            # defined samples
        self.antecedents = 0        # `implies`: samples with the antecedent true
        self.sides = set()          # `iff`: the truth values the left side took

    @property
    def largest(self):
        return len(self.models[-1].domain)


def check_statement(formula, models, kb):
    """The statement in each of `models` within the budget (a statement can fail in a small model
    and hold in a larger one, so all are checked); an AssertionError names the first
    counterexample: the model, the assignment and the tables."""
    expr = formula.expr
    deps, free, depth = analyse(expr)
    check = Check(formula.label)
    check.models = [m for m in models if cost(m, deps, free, depth) <= BUDGET]
    if not check.models:
        raise Unsupported(f'too many interpretations even for {models[0].name}: '
                          f'{cost(models[0], deps, free, depth)}')
    op = token_name(expr[0]) if isinstance(expr, list) else None
    for model in check.models:
        for tables in all_tables(model, deps):
            evaluator = Evaluator(model, deps, tables)
            for sample in itertools.product(model.domain, repeat=len(free)):
                env = dict(zip(free, sample))
                try:
                    result = evaluator.eval(expr, env)
                except Undefined:
                    continue
                check.samples += 1
                if op == 'implies' and evaluator.defined(expr[1], env):
                    check.antecedents += 1
                if op == 'iff':
                    check.sides.add(evaluator.defined(expr[1], env))
                if result is not True:
                    raise AssertionError(
                        f'"{formula.label}" fails in a model of {model.name}: '
                        f'{formula.formula_str(kb)}\n  with {env}\n  and the tables {tables}')
    return check


_loaded = {}


def load_theory(theory):
    """The knowledge base after `load THEORY`, and the statements of that file (cached: the
    statements are only read)."""
    if theory in _loaded:
        return _loaded[theory]
    kb = copy.deepcopy(kurt.initial_kb)
    with contextlib.redirect_stdout(io.StringIO()):
        kb = kurt.load_file(theory, kb)
    statements = [f for f in kb.all_theory() if os.path.basename(f.filename) == theory + '.kurt']
    _loaded[theory] = kb, statements
    return kb, statements


class TestFirstOrderSemantics(unittest.TestCase):

    PURE_MODELS = [PureModel(n) for n in (1, 2, 3, 4, 5)]
    SET_MODELS = [SetModel(UNIVERSE_5), SetModel(UNIVERSE_10), SetModel(UNIVERSE_21)]

    def check_theory(self, theory, models, expected):
        """Every statement of the theory file holds in every interpretation; returns the checks."""
        kb, statements = load_theory(theory)
        checks = {}
        for formula in statements:
            self.assertIn(formula.keyword, ('use', 'def', ''), formula.label)   # axioms and theorems
            check = check_statement(formula, models, kb)
            self.assertGreater(check.samples, 0, formula.label)
            op = token_name(formula.expr[0]) if isinstance(formula.expr, list) else None
            if op == 'implies':   # not vacuous: the antecedent is true somewhere
                self.assertGreater(check.antecedents, 0, formula.label)
            if op == 'iff':       # not trivial: the two sides are true and false together
                self.assertEqual(check.sides, {False, True}, formula.label)
            checks[formula.label] = check
        self.assertEqual(set(checks), set(expected))
        return checks

    def test_universes_are_transitive_sets_of_sets(self):
        for universe in (UNIVERSE_5, UNIVERSE_10, UNIVERSE_21):
            for s in universe:
                self.assertIsInstance(s, frozenset)
                self.assertTrue(s <= universe, 'an element outside the universe')
        self.assertEqual((len(UNIVERSE_5), len(UNIVERSE_10), len(UNIVERSE_21)), (5, 10, 21))
        self.assertTrue(UNIVERSE_5 < UNIVERSE_10 < UNIVERSE_21)
        self.assertEqual(unpair(pair(EMPTY, V2)), (EMPTY, V2))
        self.assertEqual(unpair(pair(V2, V2)), (V2, V2))
        with self.assertRaises(Undefined):
            unpair(frozenset({EMPTY}))

    def test_the_analysis_reads_the_provisos(self):
        kb, statements = load_theory('logic')
        by_label = {f.label: f for f in statements}
        deps, free, depth = analyse(by_label['forall-cond-def'].expr)
        self.assertEqual(deps, {'%C': ('$$x',), '%P': ('$$v',)})   # neither depends on the new `$$w`
        self.assertEqual((free, depth), ((), 1))
        deps, free, depth = analyse(by_label['existsunique-def'].expr)
        self.assertEqual(deps, {'%A': ('$$x',)})                   # `%A` doesn't mention `$y`
        self.assertEqual(depth, 2)
        deps, free, depth = analyse(by_label['forall-cond-elim'].expr)
        self.assertEqual(deps, {'%C': ('$$x',), '%P': ('$$v',)})
        self.assertEqual(free, ('$a',))

    def wrong_rule(self, formula, kb, label, expr):
        wrong = formula.clone(formula.expr, kb)
        wrong.expr, wrong.label = expr, label
        return wrong

    def test_the_oracle_rejects_wrong_rules(self):
        # the sanity check of the oracle itself: wrong rules, built from right ones, must fail
        kb, statements = load_theory('logic')
        by_label = {f.label: f for f in statements}
        # `(∃ $x %A) ⇒ (∀ $x %A)`
        f = by_label['existsunique-exists']
        exists = f.expr[2]
        wrong = self.wrong_rule(f, kb, 'exists-implies-forall',
                                [f.expr[0], exists, [exists[0].clone('forall'), *exists[1:]]])
        with self.assertRaisesRegex(AssertionError, 'exists-implies-forall.*2 elements'):
            check_statement(wrong, self.PURE_MODELS, kb)
        # the converse of "forall-elim", `(sub $x $a %A) ⇒ (∀ $x %A)`: a substitution in a wrong place
        f = by_label['forall-elim']
        wrong = self.wrong_rule(f, kb, 'forall-intro-from-instance', [f.expr[0], f.expr[2], f.expr[1]])
        with self.assertRaisesRegex(AssertionError, 'forall-intro-from-instance'):
            check_statement(wrong, self.PURE_MODELS, kb)
        # "existsunique-unique" without the uniqueness: `(∃ $x %A) ∧ (sub $x $a %A) ∧ (sub $x $b %A) ⇒ $a = $b`
        f = by_label['existsunique-unique']
        premise = f.expr[1]
        weak = [premise[0], [premise[1][0].clone('exists'), *premise[1][1:]], *premise[2:]]
        wrong = self.wrong_rule(f, kb, 'exists-unique', [f.expr[0], weak, f.expr[2]])
        with self.assertRaisesRegex(AssertionError, 'exists-unique'):
            check_statement(wrong, self.PURE_MODELS, kb)
        # and in the set universes: `$c ∈ $a ∪ $b ≡ $c ∈ $a ∧ $c ∈ $b`
        kb, statements = load_theory('set')
        f = next(f for f in statements if f.label == 'union')
        wrong = self.wrong_rule(f, kb, 'union-as-and', [f.expr[0], f.expr[1], [f.expr[2][0].clone('and'), *f.expr[2][1:]]])
        with self.assertRaisesRegex(AssertionError, 'union-as-and'):
            check_statement(wrong, self.SET_MODELS, kb)
        # `fst ($a, $b) = $b`
        f = next(f for f in statements if f.label == 'fst')
        wrong = self.wrong_rule(f, kb, 'fst-is-snd', [f.expr[0], f.expr[1], f.expr[1][1][1][2]])
        with self.assertRaisesRegex(AssertionError, 'fst-is-snd'):
            check_statement(wrong, self.SET_MODELS, kb)

    def test_logic_rules_hold_in_every_small_model(self):
        checks = self.check_theory('logic', self.PURE_MODELS, {
            'forall-elim', 'exists-intro', 'forall-cond-elim', 'exists-cond-intro',
            'forall-cond-def', 'exists-cond-def', 'forall-iff', 'exists-iff',
            'existsunique-def', 'existsunique-cond-def', 'existsunique-intro',
            'existsunique-exists', 'existsunique-unique',
        })
        # all 13 in every model of 1 to 5 elements (a schema variable over one bound variable:
        # 2^5 tables in the largest)
        self.assertTrue(all(c.largest == 5 for c in checks.values()), {c.label: c.largest for c in checks.values()})

    def test_equality_rules_hold_in_every_small_model(self):
        checks = self.check_theory('equality', self.PURE_MODELS, {'equal-intro', 'equal-elim'})
        self.assertTrue(all(c.largest == 5 for c in checks.values()))

    def test_set_axioms_and_theorems_hold_in_the_set_universes(self):
        checks = self.check_theory('set', self.SET_MODELS, {
            # the axioms
            'extensionality', 'separation', 'separation-in', 'empty-set', 'singleton', 'union', 'power-set',
            'pair-eq', 'triple-eq', 'fst', 'snd', 'product', 'product-pairs', 'function-space',
            'apply',
            # the definitions
            'subset', 'intersection',
            # the theorems (only their statements)
            'subset-cond', 'eq-def', 'nonempty-element', 'element-nonempty', 'in-intersection',
            'apply-in', 'function-extensionality',
        })
        # all 24 in the universe of 5 sets; those with few free variables and binders in the larger
        # ones too (the rest would take 10^5 to 10^10 samples there)
        largest = {label: c.largest for label, c in checks.items()}
        self.assertEqual({label for label in largest if largest[label] == 21}, {
            'extensionality', 'empty-set', 'singleton', 'union', 'power-set', 'fst', 'snd',
            'product-pairs', 'subset', 'intersection', 'subset-cond', 'eq-def',
            'nonempty-element', 'element-nonempty', 'in-intersection',
        })
        self.assertEqual({label for label in largest if largest[label] == 10}, {'pair-eq', 'product', 'apply-in'})
        self.assertEqual({label for label in largest if largest[label] == 5},
                         {'separation', 'separation-in', 'triple-eq', 'function-space', 'apply', 'function-extensionality'})

    def test_prop_iff_subst_holds(self):
        # the one rule of propositional.kurt that the truth tables of test_prop_semantics.py skip: a
        # substitution of a statement `%x` by `sub`, here over the two truth values
        kb, statements = load_theory('propositional')
        formula = next(f for f in statements if f.label == 'iff-subst')
        deps, free, depth = analyse(formula.expr)
        self.assertEqual(deps, {'%A': ('%x',), '%a': (), '%b': ()})
        check = check_statement(formula, [PureModel(1)], kb)
        self.assertGreater(check.antecedents, 0)


if __name__ == '__main__':
    unittest.main()
