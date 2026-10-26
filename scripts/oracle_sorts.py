#!/usr/bin/env python3
"""A semantic oracle for Kurt's sorts (doc/kurt-soundness.md §10.4).

Every step the kernel accepts with a rule of logic (propositional.kurt, logic.kurt, equality.kurt: valid in
every model) is an instance of that rule -- so the instance itself, as the kernel builds it
(`k_instance`), must be valid: true in every order-sorted model. This script checks that in random
small models: a domain of 1 to 3 objects, each sort a non-empty subset (the subsorts respected,
`any` everything), the other symbols interpreted at random (relations, total functions into their
result sort). A model in which an instance is false is a counterexample: the kernel accepted an
instance that is no consequence of the rule -- a soundness bug of the sorts (one sort per use, the
range of a binder, a substitution's sort).

A step with arithmetic -- numerals, the operations, relations and sets bound to the calculator
(`builtin + add`, `builtin Nat naturals`, ...) -- is checked in an arithmetic model: the numbers are
the rationals (exact, `Fraction`), the calculator's operations what they are (`CALCULATOR_*` of
kurt.py), other objects a few of their own, and an operation applied to something else some value
of its result sort (total operations). The numbers are infinite, so a quantifier over a sort that
contains them can't be evaluated there; free variables get random values (small rationals among
them). The calculator's own steps are checked the same way: a comparison (`calc`) true, a fact that
computes to the goal (`calc-fact`) implying it, in the arithmetic model.

Out of scope (skipped, counted): a quantifier over the numbers in a step with arithmetic, a `flat` or
`sym` operator other than the logical ones and the calculator's (their normal forms are laws), a
binder other than the quantifiers, vectors and matrices, and the rules of other theories (axioms,
not valid in every model).

usage: python3 scripts/oracle_sorts.py [--models N] FILE.kurt ...     (PYTHONPATH=src)
"""
import argparse
import contextlib
import copy
import io
import itertools
import os
import random
from fractions import Fraction
from pathlib import Path
from typing import Optional

import kurt.kurt as k
from kurt.kurt import Token

LOGIC_FILES = ('propositional.kurt', 'logic.kurt', 'equality.kurt', 'minimal.kurt')
LOGICAL_SYMMETRIC = {'and', 'or', 'iff', '='}


class Unsupported(Exception):
    pass


NUMBER_POOL = [Fraction(n) for n in (0, 1, -1, 2, 3, -2, 5)] + [Fraction(1, 2), Fraction(-3, 2), Fraction(2, 3)]


class Model:
    def __init__(self, kb, rng: random.Random, size: int, arithmetic: bool = False):
        self.kb, self.rng = kb, rng
        self.domain = [f'o{i}' for i in range(size)]
        self.sorts: dict[str, frozenset] = {}
        self.consts: dict[str, object] = {}
        self.rels: dict[tuple, bool] = {}
        self.funs: dict[tuple, object] = {}
        # (with arithmetic: the numbers are the rationals, the sort of the numbers and those above it
        # contain them -- infinitely many, so they are sampled, never enumerated)
        self.arithmetic = arithmetic
        self.num_sort = kb.pos_sort(k.NUMBERS_KEY, 0) if arithmetic else None

    def has_numbers(self, sorts) -> bool:
        if not self.arithmetic:
            return False
        sorts = [s for s in (sorts or ()) if s != 'any'] or ['any']
        return all(s == 'any' or s == self.num_sort or (self.num_sort is not None and self.kb.sort_fits(self.num_sort, s))
                   for s in sorts)

    def sample(self, sorts) -> list:
        # the values a variable of these sorts takes in a check: its objects, and numbers if it has them
        objects = sorted(self.sorts_set(sorts)) if not (self.arithmetic and sorts and self.num_sort in sorts) else []
        return objects + (NUMBER_POOL if self.has_numbers(sorts) else [])

    def value_of_sort(self, sort) -> object:
        return self.rng.choice(self.sample([sort] if sort else []))

    def sort_set(self, sort: str) -> frozenset:
        if sort in ('any', None):
            return frozenset(self.domain)
        if self.arithmetic and sort == self.num_sort:
            return frozenset()          # (the numbers: no object of their own, `sample`)
        if sort not in self.sorts:
            # below each of its supersorts (the subsorts respected), non-empty
            supers = [s for sub, s in self.kb.all_subsorts() if sub == sort]
            room = frozenset(self.domain)
            for s in supers:
                room &= self.sort_set(s)
            if not room and not self.has_numbers([sort]):
                raise Unsupported('no room for a sort')
            if not room:
                self.sorts[sort] = frozenset()
                return self.sorts[sort]
            chosen = frozenset(x for x in room if self.rng.random() < 0.6) or frozenset({self.rng.choice(sorted(room))})
            self.sorts[sort] = chosen
        return self.sorts[sort]

    def sorts_set(self, sorts) -> frozenset:
        found = frozenset(self.domain)
        for s in sorts or ():
            found &= self.sort_set(s)
        if not found and not self.has_numbers(sorts):
            raise Unsupported('an empty intersection of sorts')
        return found

    def constant(self, name: str) -> object:
        if name not in self.consts:
            self.consts[name] = self.value_of_sort(self.kb.pos_sort(name, 0))
        return self.consts[name]

    def relation(self, op: str, args: tuple) -> bool:
        key = (op, args)
        if key not in self.rels:
            self.rels[key] = self.rng.random() < 0.5
        return self.rels[key]

    def application(self, sort, args: tuple) -> object:
        # `f c` of a mapping `f`: a value of the sort Kurt gives the application -- that of `f`, as
        # for any application (`top_sorts`); of `any` it could lie outside the sort a binder ranges
        # over, and a valid instance of "forall-cond-elim" looked false (knaster-tarski.kurt, 2026-10-20)
        key = (APPLY, sort, args)
        if key not in self.funs:
            self.funs[key] = self.value_of_sort(sort)
        return self.funs[key]

    def function(self, op: str, args: tuple) -> object:
        key = (op, args)
        if key not in self.funs:
            self.funs[key] = self.value_of_sort(self.kb.pos_sort(op, 0))
        return self.funs[key]


APPLY = '$$apply'      # (the application of an object to arguments, `f c`: one function of the model for all)


def arithmetic_of(e, kb) -> bool:
    # whether `e` has symbols bound to the calculator (a numeral alone is a constant of the numbers'
    # sort, in the finite model, where quantifiers can be evaluated)
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str):
            # (the calculator's operations, relations and sets -- not its membership alone, which is
            # arithmetic only with one of its sets, `x ∈ Nat`, and that counts by the set)
            # (nor `=` and `≠`: identity, the same in the finite model)
            return any(r in k.CALCULATOR_OPERATIONS or (r in k.CALCULATOR_RELATIONS and r not in ('eq', 'ne'))
                       or r in k.CALCULATOR_SETS for r in kb.get_builtins(v))
        case [*children]:
            return any(arithmetic_of(c, kb) for c in children)
    return False


def calculator(op: str, ops: list, args: list, vals: list, m: Model, kb) -> object:
    # the calculator's meaning of `op` (its roles `ops`, kurt.py's CALCULATOR_*): exact on rationals,
    # and on anything else some value of the result sort, as an operation total on all objects
    fractions = [v for v in vals if isinstance(v, Fraction)]
    numbers = len(fractions) == len(vals)
    if any(r in k.CALCULATOR_LITERALS for r in ops):
        raise Unsupported('vectors and matrices')      # (`[1, 2]`: a literal the calculator computes with)
    for role in ops:
        if role in k.CALCULATOR_RELATIONS and len(vals) == 2:
            return k.CALCULATOR_RELATIONS[role](fractions[0], fractions[1]) if numbers else m.relation(op, tuple(vals))
        if role == k.CALCULATOR_MEMBERSHIP and len(args) == 2:
            container = args[1]
            sets = kb.get_builtins(container.value) if isinstance(container, Token) and isinstance(container.value, str) else []
            for s in sets:
                if s in k.CALCULATOR_SETS:
                    return isinstance(vals[0], Fraction) and k.CALCULATOR_SETS[s](vals[0])
            return m.relation(op, tuple(vals))
        if not numbers:
            continue
        if role == 'add' and len(vals) >= 2:
            return sum(vals, Fraction(0))
        if role == 'multiply' and len(vals) >= 2:
            result = Fraction(1)
            for v in vals:
                result *= v
            return result
        if role == 'subtract' and len(vals) == 2:
            return vals[0] - vals[1]
        if role == 'negate' and len(vals) == 1:
            return -vals[0]
        if role == 'divide' and len(vals) == 2 and vals[1] != 0:
            return vals[0] / vals[1]
        if role == 'power' and len(vals) == 2 and vals[1].denominator == 1 and abs(vals[1]) <= 12 and (vals[0] != 0 or vals[1] >= 0):
            return vals[0] ** int(vals[1])
        if role in ('transpose', 'determinant'):
            raise Unsupported('vectors and matrices')
    if any(r in k.CALCULATOR_RELATIONS or r == k.CALCULATOR_MEMBERSHIP for r in ops):
        return m.relation(op, tuple(vals))
    return m.function(op, tuple(vals))     # (not computed: `1 / 0`, an argument no number)


def role(kb, op: str) -> str:
    for r in ('negation', 'disjunction', 'equivalence', 'universal', 'existential', 'equality', 'falsum'):
        if kb.has_role(op, r):
            return r
    return {k.AND_SYMBOL: 'and', k.IMPL_SYMBOL: 'implies', 'true': 'true', 'existsunique': 'unique',
            'neq': 'neq', 'invimplies': 'invimplies'}.get(op, '')


def evaluate(e: k.Expr, m: Model, env: dict, kb) -> object:
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str):
            if v in env:
                return env[v]
            if v in ('true',) or kb.has_role(v, 'falsum'):
                return v == 'true'
            if kb.is_bool(v):
                return m.relation(v, ())
            if kb.is_var(v):
                raise Unsupported(f'a free variable `{v}`')
            if k.IMAGINARY_UNIT in kb.get_builtins(v):
                raise Unsupported('complex numbers')     # (`i`: the models have no complex numbers -- a random value of `i` refuted `i ≠ 0`)
            if k.k_takes_arguments(v, kb):
                raise Unsupported(f'an operator as a value `{v}`')     # (`f = g`: functions as objects aren't modelled)
            return m.constant(v)
        case Token(label='INT' | 'FLOAT', value=n):
            if m.arithmetic:
                return Fraction(str(n))     # (Kurt reads a number exactly)
            # (without arithmetic: a constant of the numbers' sort, two different numerals two
            # different numbers)
            key = f'#{n}'
            if key not in m.consts:
                numbers = sorted(m.sort_set(kb.pos_sort(k.NUMBERS_KEY, 0)) - set(v for c, v in m.consts.items() if c.startswith('#')))
                if not numbers:
                    raise Unsupported('more numerals than numbers in the model')
                m.consts[key] = m.rng.choice(numbers)
            return m.consts[key]
        case Token():
            raise Unsupported('a string')
        case [Token(label='SYMBOL', value=op), *args] if isinstance(op, str):
            r = role(kb, op)
            if r in ('universal', 'existential', 'unique'):
                return quantify(r, e, m, env, kb)
            if kb.is_bindop(op):
                raise Unsupported(f'the binder `{op}`')
            vals = [evaluate(a, m, env, kb) for a in args]
            if r == 'negation':
                return not vals[0]
            if r == 'and':
                return all(vals)
            if r == 'disjunction':
                return any(vals)
            if r == 'implies':
                return (not vals[0]) or vals[1]
            if r == 'invimplies':
                return (not vals[1]) or vals[0]
            if r == 'equivalence':
                return vals[0] == vals[1]
            if r == 'equality':
                return all(v == vals[0] for v in vals)
            if r == 'neq':
                return vals[0] != vals[1]
            ops = kb.get_builtins(op)
            if any(r in k.CALCULATOR_LITERALS for r in ops):
                raise Unsupported('vectors and matrices')  # (`[1, 2]`: a literal the calculator computes with)
            if ops and m.arithmetic:
                return calculator(op, ops, args, vals, m, kb)
            if (kb.is_flat(op) or kb.is_sym(op)) and op not in LOGICAL_SYMMETRIC:
                raise Unsupported(f'the normal form of `{op}`')
            if k.k_is_statement(e, kb):
                return m.relation(op, tuple(vals))
            if not k.k_takes_arguments(op, kb) and not kb.is_var(op) and kb.is_const(op) and not ops \
                    and not kb.is_bracket_placeholder(op):
                # (`f c` of a mapping `f`, an object: the application of its value, set.kurt's "apply" --
                # equal mappings have equal values)
                return m.application(kb.pos_sort(op, 0), (m.constant(op),) + tuple(vals))
            return m.function(op, tuple(vals))
    raise Unsupported(f'`{e}`')


def quantify(r: str, e, m: Model, env: dict, kb) -> bool:
    _, cond, *body = e
    x = k.k_bound(cond, kb)
    condition = None
    if isinstance(cond, list):
        condition = cond[2] if cond and isinstance(cond[0], Token) and cond[0].value == k.BOUND_SYMBOL else cond
    binder_sorts = k.k_binder_sorts(e, kb)
    if m.has_numbers(binder_sorts):
        raise Unsupported('a quantifier over the numbers in a step with arithmetic')
    rng = m.sorts_set(binder_sorts)
    def holds(d) -> Optional[bool]:
        inner = {**env, x: d}
        if condition is not None and not evaluate(condition, m, inner, kb):
            return False if r != 'universal' else None
        result = evaluate(body[-1], m, inner, kb)
        assert isinstance(result, bool)         # (the body of a quantifier is a statement)
        return result
    if r == 'universal':
        return all(holds(d) is not False for d in rng)
    found = [d for d in rng if holds(d)]
    return len(found) == 1 if r == 'unique' else bool(found)


def free_variables(e, kb) -> list[str]:
    return sorted(k.k_free(e, kb))


def valid_in(instance, m: Model, kb, cap: int = 200) -> bool:
    # true under every assignment of its free variables (each in its sort)
    names = free_variables(instance, kb)
    ranges = [[False, True] if (v[0] == '%' or kb.is_bool(v)) else m.sample(kb.variable_sorts(v)) for v in names]
    if any(not r for r in ranges):
        raise Unsupported('a variable of a sort without values here')
    product = list(itertools.product(*ranges))
    if len(product) > cap:
        product = m.rng.sample(product, cap)
    for values in product:
        if not evaluate(instance, m, dict(zip(names, values)), kb):
            return False
    return True


def rule_instance(cert, kb):
    # the instance of the whole rule, as the kernel builds it (`kernel_verify`, form `fact` or `impl`)
    deps = k.k_rule_dependencies(cert.expr, cert.rule, kb)
    relativizable = k.k_parametric_binders(cert.expr, kb)
    return k.k_instance(cert.expr, cert.values, deps, kb, relativizable | k.k_parametric_binders(cert.expr, kb))


def check_file(path: str, models: int, seed: int, stats: dict, problems: list) -> None:
    verify = k.kernel_verify
    def recording(cert, kb):
        verdict = verify(cert, kb)
        if verdict is not None:
            return verdict
        if cert.kind == 'calc':
            check_claim(cert.goal, 'calc', cert, kb)          # (a comparison that holds)
            return verdict
        if cert.kind == 'calc-fact' and cert.rule is not None:
            # (a fact that computes to the goal: the fact implies the goal)
            check_claim([Token('SYMBOL', k.IMPL_SYMBOL), cert.rule.expr, cert.goal], 'calc-fact', cert, kb)
            return verdict
        if cert.kind != 'rule' or cert.rule is None:
            return verdict
        if not (os.path.basename(str(getattr(cert.rule, 'filename', ''))) in LOGIC_FILES and cert.rule.label):
            # (a rule of logic: a labelled `use` or theorem of propositional.kurt, logic.kurt, equality.kurt -- not
            # an assumption inside one of their proofs)
            stats['other rules'] = stats.get('other rules', 0) + 1
            return verdict
        try:
            try:
                instance = rule_instance(cert, kb)
            except k.KernelReject as why:
                # (the whole rule with its `∀` premise unstripped: the kernel strips it first)
                raise Unsupported(f'the whole rule\'s instance `{why}`') from why
            check_claim(instance, cert.rule.label, cert, kb)
        except Unsupported as why:
            stats['skipped'] = stats.get('skipped', 0) + 1
            stats.setdefault('why', {})[str(why).split('`')[0].strip()] = stats.setdefault('why', {}).get(str(why).split('`')[0].strip(), 0) + 1
        except Exception as why:          # (the oracle's own trouble is no finding about Kurt)
            stats['oracle errors'] = stats.get('oracle errors', 0) + 1
            stats.setdefault('errors', []).append(f'{path}: {type(why).__name__}: {str(why)[:120]}')
        stats['steps'] = stats.get('steps', 0) + 1
        return verdict
    def check_claim(claim, label: str, cert, kb) -> None:
        # `claim` valid: true in `models` random models, arithmetic ones if it has arithmetic
        try:
            arithmetic = arithmetic_of(claim, kb)
            rng = random.Random(f'{seed}-{path}-{stats.get("steps", 0)}-{label}')
            for _ in range(models):
                m = Model(kb, rng, rng.randint(1, 3), arithmetic)
                if not valid_in(claim, m, kb):
                    where = f'{getattr(cert.rule, "filename", "")}:{getattr(cert.rule, "line", "")}' if cert.rule is not None else ''
                    problems.append((path, f'{label}" {where} kind={cert.kind} goal={k.expr_str(cert.goal, kb)}',
                                     k.expr_str(claim, kb), m.sorts, m.consts))
                    break
            key = 'checked with arithmetic' if arithmetic else 'checked'
            stats[key] = stats.get(key, 0) + 1
        except Unsupported as why:
            stats['skipped'] = stats.get('skipped', 0) + 1
            reason = str(why).split('`')[0].strip()
            stats.setdefault('why', {})[reason] = stats.setdefault('why', {}).get(reason, 0) + 1
        except Exception as why:          # (the oracle's own trouble is no finding about Kurt)
            stats['oracle errors'] = stats.get('oracle errors', 0) + 1
            stats.setdefault('errors', []).append(f'{path}: {type(why).__name__}: {str(why)[:120]}')
    k.kernel_verify = recording
    try:
        kb = copy.deepcopy(k.initial_kb)
        cwd = os.getcwd()
        full = os.path.abspath(path)
        here = os.path.dirname(full)
        os.chdir(here)
        saved_path = list(k.run_state.theory_path)
        k.run_state.theory_path = [Path(here)] + saved_path     # (`load helpers/...` next to the file)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                k.load_file(full, kb)
        except k.KurtException as why:
            stats['files with errors'] = stats.get('files with errors', 0) + 1
            stats.setdefault('errors', []).append(f'{path}: {str(why)[:160]}')
        finally:
            os.chdir(cwd)
            k.run_state.theory_path = saved_path
    finally:
        k.kernel_verify = verify


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--models', type=int, default=30)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    stats: dict = {}
    problems: list = []
    for path in a.files:
        k.run_state.kurtc_enabled = False
        check_file(path, a.models, a.seed, stats, problems)
    for path, label, instance, sorts, consts in problems:
        print(f'COUNTEREXAMPLE {path} "{label}": {instance}\n    sorts {sorts} constants {consts}')
    why = stats.pop('why', {})
    errors = stats.pop('errors', [])
    print({**stats, 'counterexamples': len(problems)})
    print('skipped because of:', dict(sorted(why.items(), key=lambda kv: -kv[1])[:8]))
    for line in errors[:10]:
        print('oracle error:', line)


if __name__ == '__main__':
    main()
