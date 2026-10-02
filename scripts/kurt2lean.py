#!/usr/bin/env python3
"""Translate a checked Kurt proof into Lean 4, so that Lean's kernel checks it again (a prototype).

    python3 scripts/kurt2lean.py proof.kurt > proof.lean
    lean proof.lean

Kurt checks the file first. While it does, every certificate of a step and every formula that a
step adds is recorded; the Lean file is written from them, without any search of its own:

- Kurt's objects are one type `Obj`, its booleans are `Prop`; a symbol becomes an `axiom` with
  the type its arity and `bool` declaration give it. `implies`, `and`, `or`, `not`, `iff`, `true`,
  `false`, `=`, `≠`, `forall`, `exists` are Lean's own.
- The rules of the loaded theories, and the `use` axioms of the file, are Lean `axiom`s (so Lean
  checks the proof relative to the same theories -- not the theories themselves).
- A step is `apply RULE (x := value) ...` with the certificate's values, then its premise from the
  cited facts with `solve_by_elim` (conjunctions and instances of `∀` facts only); Kurt's normal
  forms (`and`/`or` flat and symmetric, `=` symmetric) are allowed for by a fallback with
  `and_comm`, `and_assoc`, ... .
- A closed block is a `have ... := by intro ...; ...; exact ...` (`assume`, `case`: `intro h`;
  `let`: `intro x`; `pick`: `obtain ⟨c, h⟩`), a `show`/`proof` a `theorem`.

What isn't translated yet (conditioned quantifiers, `calc`, numbers, `def`, ...) becomes `sorry`
with a comment; `--strict-lean` makes the script fail on that instead. See the end of the output
for what was left out.
"""
from __future__ import annotations

import argparse
import contextlib
import copy
import io
import os
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'src'))
import kurt.kurt as kurt                          # noqa: E402
from kurt.kurt import Token                       # noqa: E402

# Kurt's symbols that are Lean's own
NATIVE_INFIX = {'implies': '→', 'and': '∧', 'or': '∨', 'iff': '↔', '=': '=', '≠': '≠'}
NATIVE_CONST = {'true': 'True', 'false': 'False'}
BINDERS = {'forall': '∀', 'exists': '∃'}

class Unsupported(Exception):
    pass


# --- recording what Kurt does --------------------------------------------------------------------

class Recorder:
    """While Kurt checks `path`: the certificates and the formulas added, per level (`KnowledgeBase`)."""
    def __init__(self, path: str) -> None:
        self.path = path
        self.events: list[tuple] = []          # ('cert', cert, kb) or ('formula', f, kb)
        self.parent: dict[int, int | None] = {}
        self.levels: dict[int, kurt.KnowledgeBase] = {}
        self.parent_object: dict[int, kurt.KnowledgeBase] = {}

    def note(self, kb: kurt.KnowledgeBase) -> None:
        self.levels[id(kb)] = kb
        self.parent[id(kb)] = id(kb.parent) if kb.parent is not None else None
        if kb.parent is not None:
            self.parent_object[id(kb)] = kb.parent

    def ours(self) -> bool:
        line = kurt.current_line[0]
        return line is not None and line[0] == self.path

    def run(self) -> kurt.KnowledgeBase:
        record_certificate, theory_append = kurt.record_certificate, kurt.KnowledgeBase.theory_append
        recorder = self
        def recording_certificate(cert, kb):
            result = record_certificate(cert, kb)
            if recorder.ours():
                recorder.note(kb)
                recorder.events.append(('cert', cert, kb))
            return result
        def recording_append(kb, f, *args, **kwargs):
            result = theory_append(kb, f, *args, **kwargs)
            if recorder.ours():
                recorder.note(kb)
                recorder.events.append(('formula', f, kb))
            return result
        kurt.record_certificate, kurt.KnowledgeBase.theory_append = recording_certificate, recording_append
        kurt.kurtc_enabled = False
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                kb = kurt.load_file(self.path, copy.deepcopy(kurt.initial_kb), mainstream=True)
            # a closed level is detached from its parent (`pop_level`): attach it again, so that
            # the declarations of the enclosing levels are found from it
            for kid, level in self.levels.items():
                if level.parent is None and kid in self.parent_object:
                    level.parent = self.parent_object[kid]
            return kb
        finally:
            kurt.record_certificate, kurt.KnowledgeBase.theory_append = record_certificate, theory_append


# --- Kurt expressions in Lean --------------------------------------------------------------------

def ident(name: str) -> str:
    # a Lean identifier for a Kurt symbol or variable
    if name.startswith('%%'):
        return f'P{name[2:]}'
    if name.startswith('$$'):
        return f'x{name[2:]}'
    if name.startswith('%'):
        return f'P_{ident(name[1:])}'
    if name.startswith('$'):
        return f'x_{ident(name[1:])}'
    if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name):
        return f'k_{name}' if name in LEAN_KEYWORDS else name
    return 'k_' + ''.join(c if c.isalnum() else f'u{ord(c):x}' for c in name)

LEAN_KEYWORDS = {'fun', 'theorem', 'axiom', 'def', 'have', 'show', 'by', 'at', 'in', 'let', 'from',
                 'with', 'match', 'do', 'if', 'then', 'else', 'Type', 'Prop', 'Sort', 'exact', 'intro',
                 'calc', 'open', 'end', 'namespace', 'section', 'variable', 'example', 'where', 'deriving',
                 'instance', 'structure', 'class', 'mut', 'return', 'for', 'unless', 'try', 'catch'}

class Translator:
    def __init__(self, kb: kurt.KnowledgeBase) -> None:
        self.kb = kb                                # for the symbols' declarations
        self.symbols: dict[str, tuple[str, str]] = {}   # Kurt symbol -> its Lean name and type
        self.prop_args: dict[str, set[int]] = {}        # ... and its arguments that are `Prop`
        self.missing: list[str] = []                # what wasn't translated

    def is_bool(self, name: str) -> bool:
        return self.kb.is_bool(name) or name.startswith('%')

    def declared_arity(self, name: str, kb: kurt.KnowledgeBase) -> int:
        if kb.is_infix(name):
            return 2
        if kb.is_prefix(name) or kb.is_postfix(name):
            return 1
        return kb.get_arity(name)

    def symbol(self, name: str, kb: kurt.KnowledgeBase, nargs: int | None = None, args: list | None = None) -> str:
        # a non-native constant: declare it once, with the type its arity and `bool` give it -- one
        # per number of arguments, if it has several (`-` is infix and prefix: `a - b`, `- a`)
        arity = self.declared_arity(name, kb)
        if nargs is not None and nargs != arity and ((kb.is_infix(name) and kb.is_prefix(name)) or arity == 0):
            arity = nargs                    # `- a` besides `a - b`; or applied without a declared arity (`Pow A`)
        key = name if arity == self.declared_arity(name, kb) else f'{name}/{arity}'
        lean = ident(name) if key == name else f'{ident(name)}_{arity}'
        # the type of an argument: `Prop` if `bool` says so, or if it gets a boolean (Kurt's light
        # type check allows `□ X` with `bool b` only for the result)
        sig = kb.bool_sig(name)
        props = self.prop_args.setdefault(key, set(i for i in range(1, arity + 1) if i in sig))
        for i, a in enumerate(args or [], start=1):
            if kurt.bool_expr(a, kb):
                props.add(i)
        types = ['Prop' if i in props else 'Obj' for i in range(1, arity + 1)]
        self.symbols[key] = (lean, ' → '.join(types + ['Prop' if 0 in sig else 'Obj']))
        return lean

    def var_type(self, name: str) -> str:
        result = 'Prop' if self.is_bool(name) else 'Obj'
        n = getattr(self, 'function_arity', {}).get(name, 0)
        return ' → '.join(['Obj'] * n + [result])

    def expr(self, e, kb: kurt.KnowledgeBase, schema: dict[str, list[str]] | None = None, bound: tuple[str, ...] = ()) -> str:
        # `schema`: the schema variables that are functions of bound variables, with their parameters
        schema = schema or {}
        match e:
            case Token(label='SYMBOL', value=v) if isinstance(v, str):
                if v in NATIVE_CONST:
                    return NATIVE_CONST[v]
                if v == '_':
                    return '_'
                if v in schema:
                    params = schema[v]
                    return f"({ident(v)} {' '.join(ident(p) for p in params)})" if params else ident(v)
                if v.startswith(('$', '%')) or kb.is_var(v) or v in bound:
                    return ident(v)
                return self.symbol(v, kb)
            case Token(label='INT' | 'FLOAT'):
                raise Unsupported('numbers')
            case Token():
                raise Unsupported(f'the token `{e.value}`')
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), a, A] if op == kurt.SUB_SYMBOL:
                return f'((fun ({ident(x)} : {self.var_type(x)}) => {self.expr(A, kb, schema, bound + (x,))}) {self.expr(a, kb, schema, bound)})'
            case [Token(label='SYMBOL', value=op), cond, body] if op in BINDERS:
                if not (isinstance(cond, Token) and isinstance(cond.value, str)):
                    raise Unsupported('quantifiers with a condition')
                x = cond.value
                return f'({BINDERS[op]} ({ident(x)} : {self.var_type(x)}), {self.expr(body, kb, schema, bound + (x,))})'
            case [Token(label='SYMBOL', value='not'), a]:
                return f'(¬ {self.expr(a, kb, schema, bound)})'
            case [Token(label='SYMBOL', value=op), *args] if op in NATIVE_INFIX and len(args) >= 2:
                if len(args) > 2 and op not in ('and', 'or'):
                    raise Unsupported(f'`{op}` with {len(args)} arguments')
                return '(' + f' {NATIVE_INFIX[op]} '.join(self.expr(a, kb, schema, bound) for a in args) + ')'
            case [Token(label='SYMBOL', value=op), *args] if isinstance(op, str) and kb.is_bindop(op):
                raise Unsupported(f'the binder `{op}`')
            case [Token(label='SYMBOL', value=v), *args] if args and isinstance(v, str) and not (v.startswith(('$', '%')) or kb.is_var(v) or v in bound or v in schema):
                return '(' + ' '.join([self.symbol(v, kb, len(args), args)] + [self.expr(a, kb, schema, bound) for a in args]) + ')'
            case [head, *args] if args:
                return '(' + ' '.join([self.expr(head, kb, schema, bound)] + [self.expr(a, kb, schema, bound) for a in args]) + ')'
        raise Unsupported(f'the expression `{kurt.expr_str(e, kb)}`')

    # the schema variables of a formula, as Lean binders --------------------------------------------

    def schema_of(self, e, kb: kurt.KnowledgeBase) -> tuple[list[str], dict[str, list[str]]]:
        # the free variables of `e` in the order of their first occurrence, and those that occur
        # in the scope of bound variables (a `%A` under `∀ x`, or the body of `sub x a`): their
        # parameters, the bound variables at every occurrence
        order: list[str] = []
        scopes: dict[str, list[tuple[str, ...]]] = {}
        self.function_arity: dict[str, int] = getattr(self, 'function_arity', {})
        def walk(t, bound: tuple[str, ...]) -> None:
            match t:
                case [Token(label='SYMBOL', value=v), *args] if args and isinstance(v, str) and kb.is_var(v) and v not in bound:
                    self.function_arity[v] = len(args)      # e.g. `$a ∘ $b` with the variable `∘`
                    walk(t[0], bound)
                    for a in args:
                        walk(a, bound)
                case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v) and v not in bound:
                    if v not in order:
                        order.append(v)
                    scopes.setdefault(v, []).append(bound)
                case Token():
                    pass
                case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), a, A] if op == kurt.SUB_SYMBOL:
                    walk(a, bound)
                    walk(A, bound + (x,))
                case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                    x = cond.value if isinstance(cond, Token) else None
                    if x is None:
                        raise Unsupported('quantifiers with a condition')
                    for b in body:
                        walk(b, bound + (x,))
                case [*children]:
                    for c in children:
                        walk(c, bound)
        walk(e, ())
        schema: dict[str, list[str]] = {}
        for v in order:
            inner = [s for s in scopes[v] if s]
            if inner and self.is_bool(v):
                params = list(dict.fromkeys(x for s in scopes[v] for x in s))
                if any(set(s) != set(params) for s in scopes[v]):
                    raise Unsupported(f'`{v}` at places with different bound variables')
                schema[v] = params
        return order, schema

    def statement(self, e, kb: kurt.KnowledgeBase) -> tuple[str, list[str], dict[str, list[str]]]:
        # `∀ (free variables), e`, and the free variables and the parametrized ones
        order, schema = self.schema_of(e, kb)
        binders = []
        for v in order:
            t = self.var_type(v)
            if v in schema and schema[v]:
                t = ' → '.join(['Prop' if self.is_bool(p) else 'Obj' for p in schema[v]] + [t])
            binders.append(f'({ident(v)} : {t})')
        body = self.expr(e, kb, schema)
        return (f"∀ {' '.join(binders)}, {body}" if binders else body), order, schema

    def value(self, v: str, value, schema: dict[str, list[str]], kb: kurt.KnowledgeBase, scope: set[str] = frozenset()) -> str:
        # a variable of the value that has no value of its own and isn't introduced (`scope`)
        # stands for anything: `_`, for Lean to fill in
        params = schema.get(v, [])
        value = self.holes(value, kb, set(params) | set(scope))
        if params:
            return f"(fun {' '.join(f'({ident(p)} : {self.var_type(p)})' for p in params)} => {self.expr(value, kb, bound=tuple(params))})"
        return self.expr(value, kb)

    def holes(self, e, kb: kurt.KnowledgeBase, known: set[str], bound: frozenset[str] = frozenset()):
        match e:
            case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v) and v not in known and v not in bound:
                return Token('SYMBOL', '_')
            case Token():
                return e
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op) and isinstance(cond, Token):
                return [e[0], cond, *(self.holes(b, kb, known, bound | {cond.value}) for b in body)]
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), a, A] if op == kurt.SUB_SYMBOL:
                return [e[0], e[1], self.holes(a, kb, known, bound), self.holes(A, kb, known, bound | {x})]
            case [*children]:
                return [self.holes(c, kb, known, bound) for c in children]
        return e


# --- writing the Lean file -------------------------------------------------------------------------

AC = 'and_comm, and_assoc, and_left_comm, or_comm, or_assoc, or_left_comm, eq_comm'

class LeanWriter:
    def __init__(self, recorder: Recorder, kb: kurt.KnowledgeBase, source: str) -> None:
        self.r = recorder
        self.t = Translator(kb)
        self.source = source
        self.axioms: dict[int, str] = {}        # Formula.id -> its Lean declaration (rules, `use`)
        self.names: dict[int, str] = {}         # Formula.id -> its Lean name
        self.decls: list[str] = []              # the axioms, in the order they are first needed
        self.lines: list[str] = []              # the theorems
        self.sorries = 0
        self.globals: set[str] = set()          # the names of axioms and top-level theorems (not `have`s)
        self.scope: set[str] = set()            # the Kurt variables introduced at this point of the proof

    def name(self, f) -> str:
        return self.names.setdefault(f.id, f'f{f.id}')

    def require(self, f, kb) -> str:
        # a formula used by a step: an axiom unless the file proves it (then it has a name already)
        if f.id in self.names:
            return self.names[f.id]
        name = self.name(f)
        try:
            stmt, _, _ = self.t.statement(f.simplified_expr if f.direction_of is None else f.direction_of, kb)
            where = f'{os.path.basename(f.filename)}:{f.line}' + (f' "{f.label}"' if f.label else '')
            self.decls.append(f'axiom {name} : {stmt}   -- {where}')
            self.globals.add(name)
        except Unsupported as e:
            self.decls.append(f'axiom {name} : True   -- not translated ({e}): {kurt.expr_str(f.simplified_expr, kb)}')
            self.globals.add(name)
            self.t.missing.append(f'the formula `{kurt.expr_str(f.simplified_expr, kb)}` ({e})')
        return name

    def step(self, cert, kb, indent: str) -> list[str]:
        # tactic lines proving the goal of a certificate
        if cert.kind == 'top':
            return [f'{indent}trivial']
        if cert.kind != 'rule':
            raise Unsupported(f'a step `{cert.kind}`')
        rule = cert.rule
        name = self.require(rule, kb)
        e = rule.simplified_expr
        if rule.direction_of is not None:
            iff = rule.direction_of
            order, schema = self.t.schema_of(iff, kb)
            mp = e[1] is iff[1]
        else:
            order, schema = self.t.schema_of(e, kb)
        args = ' '.join(f'({ident(v)} := {self.t.value(v, cert.values[v], schema, kb, self.scope)})'
                        for v in order if v in cert.values)
        term = f'({name} {args})' if args else name
        if rule.direction_of is not None:
            term = f'({term}).{"mp" if mp else "mpr"}'
        names = [self.require(f, kb) for f in cert.facts]
        facts = ', '.join(names)
        elim = f'solve_by_elim [And.intro{", " + facts if facts else ""}]'
        # the last resort: Lean's `grind`, with just the rule and the facts of the certificate (it
        # uses the local ones by itself) -- for Kurt's normal forms inside a fact, like `or` reordered
        filled = []
        for f, n in zip(cert.facts, names):
            f_order, f_schema = self.t.schema_of(f.simplified_expr, kb)
            f_args = ' '.join(f'({ident(v)} := {self.t.value(v, cert.values[v], f_schema, kb, self.scope)})' for v in f_order if v in cert.values)
            filled.append(f'have := {n} {f_args}' if f_args else f'have := {n}')
        grind = '(' + '; '.join([f'have r := {term}'] + filled + ['grind']) + ')'
        if cert.form == 'fact':
            return [f'{indent}first | exact {term} | (have r := {term}; simp only [{AC}] at r ⊢; exact r) | {grind}']
        return [f'{indent}first',
                f'{indent}  | (apply {term} <;> {elim})',
                f'{indent}  | (have r := {term}; simp only [{AC}] at r ⊢; apply r <;> {elim})',
                f'{indent}  | {grind}']

    def proof_of(self, f, kb_id: int, indent: str) -> list[str]:
        # tactic lines proving the formula `f` added to level `kb_id`, from what happened before
        just = self.justification.get(f.id)
        if just is None:
            raise Unsupported('no certificate')
        kind, payload = just
        if kind == 'certs':
            certs = payload
            kb = self.r.levels[kb_id]
            names = list(dict.fromkeys(v for c in certs for v in self.t.schema_of(c.goal, kb)[0]))
            intro = [f"{indent}intro {' '.join(ident(v) for v in names)}"] if names else []
            saved = set(self.scope)
            self.scope |= set(names)
            try:
                if len(certs) == 1:
                    return intro + self.step(certs[0], kb, indent)
                lines = intro + [f"{indent}refine ⟨{', '.join('?_' for _ in certs)}⟩"]
                for c in certs:
                    lines += [f'{indent}·'] + self.step(c, self.r.levels[kb_id], indent + '  ')
                return lines
            finally:
                self.scope = saved
        if kind == 'block':
            cert, block_id = payload
            return self.block(cert, block_id, f, indent)
        if kind == 'proof':
            block_id, last = payload
            body = self.body(block_id, indent)
            return body + [f'{indent}exact {self.name(last)}']
        raise Unsupported(kind)

    def block(self, cert, block_id: int, f, indent: str) -> list[str]:
        block = self.r.levels[block_id]
        parent = self.r.levels.get(self.r.parent.get(block_id), block)
        goal_vars = self.t.schema_of(cert.goal, parent)[0]
        intros = [ident(v) for v in goal_vars]
        saved = set(self.scope)
        self.scope |= set(goal_vars)
        try:
            return self.block_lines(cert, block, block_id, intros, indent)
        finally:
            self.scope = saved

    def block_lines(self, cert, block, block_id: int, intros: list[str], indent: str) -> list[str]:
        lines = [f"{indent}intro {' '.join(intros)}"] if intros else []
        hyps = [g for g in self.formulas[block_id] if g.id not in self.justification]
        match cert.kind:
            case 'impl-intro' | 'not-intro':
                assumption = hyps[0] if hyps else None
                if assumption is None:
                    lines.append(f'{indent}intro _')
                else:
                    lines += self.restate(assumption, block, indent)
            case 'forall-intro':
                consts = [a.value for a in block.mode_args if isinstance(a, Token)]
                if len(consts) != len(block.mode_args):
                    raise Unsupported('`let` with a condition')
                # (a boolean variable stays free in the result, without `∀`: introduced above already)
                new = [ident(c) for c in consts if ident(c) not in intros]
                if new:
                    lines.append(f"{indent}intro {' '.join(new)}")
            case 'exists-elim':
                witness = block.mode_args[0].value
                source = self.require(block.pick_source, block)
                lines.append(f'{indent}obtain ⟨{ident(witness)}, h_{self.name(block.pick_fact)}⟩ := {source}')
                lines += self.restate(block.pick_fact, block, indent, introduced=f'h_{self.name(block.pick_fact)}')
            case _:
                raise Unsupported(f'the block rule `{cert.kind}`')
        lines += self.body(block_id, indent)
        lines.append(f'{indent}exact {self.name(cert.rule)}')
        return lines

    def restate(self, f, kb, indent: str, introduced: str | None = None) -> list[str]:
        # an assumption (introduced by `intro`, or by `obtain` as `introduced`), stated again as Kurt
        # stores it: with the names of its variables that the certificates use
        h = introduced or f'h_{self.name(f)}'
        lines = [] if introduced else [f'{indent}intro {h}']
        stmt, order, _ = self.t.statement(f.simplified_expr, kb)
        if order:
            return lines + [f'{indent}have {self.name(f)} : {stmt} := by intros; first | exact {h} | apply {h}']
        return lines + [f'{indent}have {self.name(f)} : {stmt} := {h}']

    def body(self, kb_id: int, indent: str) -> list[str]:
        # `have`s for the formulas of a block that steps or closed blocks gave
        lines = []
        kb = self.r.levels[kb_id]
        for g in self.formulas.get(kb_id, []):
            if g.id not in self.justification:
                continue                         # an assumption, a `pick` fact: from `intro`/`obtain`
            stmt, _, _ = self.t.statement(g.simplified_expr, kb)
            lines.append(f'{indent}have {self.name(g)} : {stmt} := by')
            lines += self.proof_of(g, kb_id, indent + '  ')
        return lines

    def analyse(self) -> None:
        # which certificates and blocks justify which formula, per level
        self.formulas: dict[int, list] = {}
        self.justification: dict[int, tuple] = {}
        pending: dict[int, list] = {}            # certificates waiting for their formula, per level
        closed: dict[int, tuple] = {}            # the last block closed below a level: (block id, its last formula)
        for kind, x, kb in self.r.events:
            kid = id(kb)
            if kind == 'cert':
                if x.block is not None:
                    target = self.r.parent[kid]
                    pending.setdefault(target, []).append(('block', x, kid))
                    if x.block.theory:
                        closed[target] = (kid, x.block.theory[-1])
                else:
                    pending.setdefault(kid, []).append(('cert', x, kid))
                continue
            f = x
            self.formulas.setdefault(kid, []).append(f)
            if kb.mode_str == 'proof' and self.r.parent.get(kid) is not None:
                closed[self.r.parent[kid]] = (kid, f)        # the last line of a `proof` so far
            waiting = pending.get(kid, [])
            same = [w for w in waiting if kurt.equal_expr(w[1].goal, f.expr, kb, keep_order=False)
                    or kurt.equal_expr(w[1].goal, f.simplified_expr, kb, keep_order=False)]
            if same:
                w = same[0]
                waiting.remove(w)
                self.justification[f.id] = ('block', (w[1], w[2])) if w[0] == 'block' else ('certs', [w[1]])
            elif waiting and all(w[0] == 'cert' for w in waiting) and f.keyword == '':
                self.justification[f.id] = ('certs', [w[1] for w in waiting])   # a conjunction, one certificate per conjunct
                waiting.clear()
            elif f.keyword == '' and kid in closed and self.r.levels[closed[kid][0]].mode_str == 'proof' \
                    and kurt.equal_expr(closed[kid][1].expr, f.expr, kb, keep_order=False):
                self.justification[f.id] = ('proof', closed.pop(kid))   # what a `qed` gives
            # otherwise a hypothesis (`use`, an assumption, a `pick` fact) or something not recorded

    def write(self) -> str:
        self.analyse()
        top = id(next(kb for kind, x, kb in self.r.events if kb.is_load_boundary)) if self.r.events else None
        out = []
        for kind, x, kb in self.r.events:
            if kind != 'formula' or id(kb) != top:
                continue
            f = x
            if f.id not in self.justification:
                if f.keyword in ('use', ''):
                    self.require(f, kb)          # an axiom of the file
                continue
            name = self.name(f)
            try:
                stmt, _, _ = self.t.statement(f.simplified_expr, kb)
                proof = self.proof_of(f, id(kb), '  ')
                self.globals.add(name)
                out += [f'-- line {f.line}: {f.input_line}', f'theorem {name} : {stmt} := by'] + proof + ['']
            except Unsupported as e:
                self.sorries += 1
                self.t.missing.append(f'line {f.line} `{f.input_line}` ({e})')
                stmt_text = None
                try:
                    stmt_text, _, _ = self.t.statement(f.simplified_expr, kb)
                except Unsupported:
                    pass
                out += [f'-- line {f.line}: {f.input_line} -- not translated: {e}',
                        f'theorem {name} : {stmt_text or "True"} := by sorry', '']
        header = [f'-- {self.source}, translated from Kurt by kurt2lean.py (a prototype); check with `lean`',
                  'set_option linter.unusedSimpArgs false   -- the fallback for Kurt\'s normal forms lists all of them',
                  'namespace Kurt   -- Kurt\'s symbols, apart from Lean\'s own names (`Nat`, `Pow`, ...)', '',
                  'axiom Obj : Type', '']
        symbols = [f'axiom {lean} : {t}' for lean, t in self.t.symbols.values()]
        footer = []
        if self.t.missing:
            footer = ['', '/- not translated:'] + [f'   - {m}' for m in self.t.missing] + ['-/']
        return '\n'.join(header + symbols + [''] + self.decls + [''] + out + ['end Kurt'] + footer) + '\n'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('file', help='the Kurt file')
    parser.add_argument('-o', '--output', help='the Lean file (default: stdout)')
    parser.add_argument('--strict-lean', action='store_true', help='fail if anything is not translated')
    args = parser.parse_args()
    path = os.path.abspath(args.file if args.file.endswith('.kurt') else args.file + '.kurt')
    recorder = Recorder(path)
    try:
        kb = recorder.run()
    except kurt.KurtException as e:
        sys.exit(f'Kurt does not accept {args.file}:\n{e.msg}')
    writer = LeanWriter(recorder, kb, os.path.basename(path))
    text = writer.write()
    if args.output:
        Path(args.output).write_text(text, encoding='utf-8')
    else:
        sys.stdout.write(text)
    if writer.t.missing:
        print(f'kurt2lean: {len(writer.t.missing)} thing(s) not translated, see the end of the file', file=sys.stderr)
        if args.strict_lean:
            sys.exit(1)


if __name__ == '__main__':
    main()
