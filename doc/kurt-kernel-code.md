# Kurt's kernel, read as code

A literate reading of the kernel: the part of `src/kurt/kurt.py` that decides whether a step
of a proof counts. Each piece of the code is cited here as it is, with the reasoning next to it.
`doc/kurt-kernel.md` explains the same kernel by what it *checks*, with examples and diagrams, and
`doc/kurt-soundness.md` §9 says why it is sound; this document explains the *implementation*,
function by function, in the order in which one would read it, not the order of the file.

**The citations are the code.** Each chunk below follows a directive like
`<!-- cite: def k_bound -->` (visible in the source of this document, not when it is rendered), and
`scripts/kernel_doc.py` takes the chunk from `kurt.py` -- a whole top-level definition, or the lines
from one prefix to another, inside a named definition. `tests/test_kernel_literate.py` fails when a
chunk no longer is the code, or when a kernel function has no chunk; after a change to the kernel,
`python3 scripts/kernel_doc.py --update` writes the chunks again, and the prose must be read again.
So this document can't drift from the kernel unnoticed, which is the point of citing code instead
of describing it. (Written 2026-10-16, for Kurt 0.9.0.)

The kernel is about 620 lines: `Certificate`, `KernelEnv`, `kernel_verify`, `kernel_verify_block`,
and the helpers `k_*`. It calls a few trusted functions of the rest of Kurt, named in §9.

## 1. The contract: every step goes through `record_certificate`

The search (unification, `sub` matching, stripping quantifiers, blocked and eigen variables) is
large and not trusted. When it has found how a line follows -- which rule, which facts, which
values for the variables -- it builds a `Certificate` and calls `record_certificate`. Nothing else
makes a fact: `derive_expr`, `impl_elim`, the closing of a block, the shortcuts for `true`, `calc`
and `todo` all end here.

<!-- cite: def record_certificate -->
```python
def record_certificate(cert: Certificate, kb: KnowledgeBase) -> Certificate:
    # the kernel checks every step; `cert` shows the certificates of a line
    try:
        problem = kernel_verify(cert, kb)
    except Exception as e:      # a crash of the kernel counts as a rejection
        problem = f'the kernel failed: {type(e).__name__}: {e}'
    if problem is not None:
        raise KernelError(f'KernelError: the kernel rejects the step to `{expr_str(cert.goal, kb)}`: {problem} -- '
                          f'the search accepted it, so this is a bug in Kurt; please report it, with this file')
    if run_state.current_line[0] is not None:
        run_state.certificates_by_line.setdefault(run_state.current_line[0], []).append((cert, problem))
    return cert
```

Three things to notice. The kernel is called *every* time, not only in a test or with an option.
A crash of the kernel counts as a rejection (`except Exception`): a bug in the kernel can make Kurt
refuse a proof, never accept one. And a rejection is a `KernelError`, whose text says what it is:
a disagreement between the search and the kernel, a bug in one of them.

<!-- cite: class KernelError -->
```python
class KernelError(KurtException):
    # the kernel rejects a step that the search accepted: the two disagree, which is a bug in one
    # of them -- the step doesn't count. Its kind `KernelError` isn't one an `expect` can name, so
    # it always stops a file (in the shell, only the line fails).
    def __init__(self, msg: str) -> None:
        super().__init__(msg, kind='KernelError')
```

`KernelError` is a `KurtException` with a kind that `expect` can't name, so no `expect` block
catches it (`tests/test_kernel.py`, `test_expect_does_not_catch_it`): the file stops. The accepted
certificates of a line are kept in `run_state.certificates_by_line`, which `cert` shows, the hover
of the editors renders, `.kurtc` stores (§8) and `kurt --lean` translates.

## 2. What a step hands over: `Certificate`

A certificate is a plain record of what the search claims, in terms the kernel can check without
searching: the goal, the rule, how the rule is read, the values of the variables, the facts.

<!-- cite: class Certificate ... block: Optional[KnowledgeBase] = None -->
```python
class Certificate:
    kind: str                           # 'rule', or 'top', 'calc', 'calc-fact', 'todo', or a block rule (see `block`)
    goal: Expr                          # the claim, as `derive_expr` sees it (outer `∀`s removed, variables renamed)
    fixed: frozenset[str]               # the free variables of the goal, which stand for anything: they get no value
    rule: Optional[Formula] = None      # the fact or rule used ('rule'), the fact that computes to the goal ('calc-fact'), the bare `todo` ('todo')
    form: str = ''                      # how the rule is read: 'fact' (the goal is an instance) or 'impl' (premise ⇒ conclusion)
    expr: Optional[Expr] = None         # the rule as read: its `simplified_expr`, or one direction `L ⇒ R` of an `iff`
    premise_fresh: tuple[str, ...] = () # the fresh names for the outer `∀`s of the premise, in order
    conclusion_fresh: tuple[str, ...] = ()  # ... and for those of the conclusion
    values: dict[str, Expr] = field(default_factory=dict)   # the values of the variables (of the rule and of the facts)
    facts: list[Formula] = field(default_factory=list)      # the facts that match the parts of the premise
    fact_fresh: list[tuple[str, ...]] = field(default_factory=list)  # fresh names for `∀` parts of the premise, matched without their `∀`s
    block: Optional[KnowledgeBase] = None   # for closing a block ('impl-intro', 'not-intro', 'forall-intro', 'exists-elim'): its level
```

The fields, by the kinds of steps:

- `kind` is `'rule'` for the ordinary step (the goal is an instance of a fact, or follows from a
  rule with premises), `'top'` for `true`, `'calc'` for a computed comparison, `'calc-fact'` for a
  fact that computes to the goal, `'todo'` for an admitted line, `'case-elim'` for a `case` block
  with more than two alternatives, and one of `'impl-intro'`, `'not-intro'`, `'forall-intro'`,
  `'exists-elim'` when a block closes (then `block` is the block's level, §6).
- `goal` is the claim as the search saw it: the outer `∀`s of the line removed, their variables
  renamed. `fixed` names the free variables of the goal: they stand for anything and must not get
  a value (a goal `P($x)` is proved for all `$x`, not for one).
- `rule` is the `Formula` used (for a `'todo'` the `todo` line itself, so that `--foundation` can
  name it), `expr` the expression of the rule as the search read it -- its
  `simplified_expr`, or one direction `L ⇒ R` of an `iff` -- and `form` says whether the goal is an
  instance of it (`'fact'`) or follows from its conclusion with its premise (`'impl'`).
- `premise_fresh` and `conclusion_fresh` are the fresh names the search gave to the variables of
  the outer `∀`s of the premise and of the conclusion, in order; `fact_fresh` the names for `∀`s
  of parts of the premise that were matched without their `∀`s. The kernel strips the same `∀`s
  with the same names (`k_strip`) and then checks that those names are really fresh (§4.5).
- `values` are the values of the variables, of the rule and of the facts, as a map from the name
  to an expression; `facts` the facts that match the parts of the premise.

The method `step` only renders a certificate as a reason (`equal-elim` with `11`, `10`; `2` with
`3`; `forall-intro` with `13-14`); it decides nothing:

<!-- cite: Certificate :: def step ... return self.kind, ([] if own_lines else [lines]), not own_lines -->
```python
def step(self, filename: str, own_lines: bool = False) -> tuple[str, list[str], bool]:
    # the rule and the lines (or labels) it is applied to, e.g. `equal-elim` with `11`, `10`;
    # `2` with `3` (the implication of line 2 with the fact of line 3); `forall-intro` with
    # `13-14` (the lines of the block; without them if the step is numbered by them,
    # `own_lines`) -- and whether they are written in brackets (`Reason` renders it, `cert`
    # shows the long form)
    ref = lambda f: line_ref(f, filename)
    match self.kind:
        case 'rule':
            assert self.rule is not None
            if self.form == 'fact':
                return ref(self.rule), [], False
            return ref(self.rule), [ref(f) for f in self.facts], True
        case 'top':
            return 'top-intro', [], False
        case 'calc':
            return 'calc', [], False
        case 'calc-fact':
            assert self.rule is not None
            return 'calc', [ref(self.rule)], True
        case 'todo':
            return 'todo', [], False
        case 'case-elim':
            return 'case-elim', [ref(f) for f in self.facts], True
    assert self.block is not None and self.rule is not None
    lines = block_lines(self.block, self.rule)
    if self.kind == 'exists-elim' and self.block.pick_source is not None:
        return 'exists-elim', [ref(self.block.pick_source)] + ([] if own_lines else [lines]), True
    return self.kind, ([] if own_lines else [lines]), not own_lines
```

A certificate is a record of a checked step and is never changed afterwards; an exported fact
keeps its certificates across `load` (the `Reason` of a step carries them, for `--foundation`), so
a deep copy of a certificate is the certificate itself:

<!-- cite: Certificate :: def __deepcopy__ ... return self -->
```python
def __deepcopy__(self, memo: dict) -> 'Certificate':
    # the record of a checked step, never changed afterwards: a copied fact (its `Reason`, in an
    # `ExportBundle`) keeps pointing at the same one, with the facts of the file that proved it (`foundation`)
    return self
```

## 3. What the kernel may see: `KernelEnv`

A `KnowledgeBase` is mutable and large. The kernel doesn't get it: it gets a `KernelEnv`, a
read-only view that allows only the lookups the kernel needs, and remembers each answer for the
whole check, so that the environment can't change under the kernel's feet, and so that nothing
can be changed through it.

The lookups are listed in a `Protocol`, `KbReader`, as read-only views: a sequence where the
environment hands out a copy of a list, a set that can't be changed where it hands out a frozen
set. The functions of the kernel, and the trusted functions of the rest of Kurt that it calls
(`normalize_expr`, `expr_str`, ...), take a `KbReader` and never a `KnowledgeBase`. What such a
function does with its `kb` is checked against the list by the type checker (`pyright`): a kernel
function that reached for another member, or tried to change what it read, is rejected before it
could fail at run time. A `KnowledgeBase` has every member, so the search can pass one too; so has
the `KernelEnv`, which is what the kernel gets -- the type checker verifies that, too.

<!-- cite: class KbReader -->
```python
class KbReader(Protocol):
    # what the kernel may read of a knowledge base: the members of `KernelEnv` (and no others:
    # `tests/test_kernel_env.py` compares them), as read-only views -- `KernelEnv` hands out a copy
    # of a list, a frozen set for a set, a snapshot for a generator. A `KnowledgeBase` has all of
    # them, so the search can pass one as well. A function of the kernel, and every trusted function
    # it calls, takes a `KbReader` and never a `KnowledgeBase`: what it does with it is then checked
    # against this list (soundness §9: the kernel can read the knowledge base, never change it)
    # the symbols
    def is_var(self, s: str) -> bool: ...
    def is_bool(self, s: str) -> bool: ...
    def bool_sig(self, s: str) -> Sequence[int]: ...
    def variable_sorts(self, symbol: str) -> AbstractSet[str]: ...
    def pos_sort(self, symbol: str, position: int) -> Optional[str]: ...
    def pos_sorts(self, symbol: str, position: int) -> frozenset[str]: ...
    def all_subsorts(self) -> frozenset[tuple[str, str]]: ...
    def generalized_sorts(self, symbol: str) -> frozenset[str]: ...
    def binder_sorts(self, node: Expr) -> frozenset[str]: ...
    def is_bindop(self, s: str) -> bool: ...
    def is_const(self, s: str) -> bool: ...
    def is_known(self, s: str) -> bool: ...
    def is_used(self, s: str) -> bool: ...
    def is_fixed_var(self, s: str) -> bool: ...
    def is_vocabulary_symbol(self, s: str) -> bool: ...
    def get_arity(self, fun: str) -> int: ...
    def is_flat(self, s: str) -> bool: ...
    def is_sym(self, s: str) -> bool: ...
    def all_flat(self) -> Iterator[str]: ...
    def get_builtins(self, symbol: str) -> Sequence[str]: ...
    def has_role(self, symbol: object, role: str) -> bool: ...
    def role_symbol(self, role: str) -> Optional[str]: ...
    def calculate(self, e: Expr) -> Expr: ...
    def is_operator(self, s: str) -> bool: ...
    def is_infix(self, s: str) -> bool: ...
    def is_prefix(self, s: str) -> bool: ...
    def is_postfix(self, s: str) -> bool: ...
    def is_bracket_placeholder(self, s: str) -> bool: ...
    # the facts, and how the block was opened
    def all_theory(self) -> Iterator[Formula]: ...
    @property
    def theory(self) -> Sequence[Formula]: ...
    @property
    def const(self) -> AbstractSet[str]: ...
    @property
    def mode_str(self) -> str: ...
    @property
    def mode_args(self) -> Sequence[Expr]: ...
    @property
    def let_names(self) -> Sequence[str]: ...
    @property
    def fixed_vars(self) -> AbstractSet[str]: ...
    @property
    def pick_source(self) -> Optional[Formula]: ...
    @property
    def pick_fact(self) -> Optional[Formula]: ...
    # how expressions are printed (in a message)
    @property
    def format(self) -> Format: ...
    @property
    def calc(self) -> bool: ...
```

<!-- cite: class KernelEnv -->
```python
class KernelEnv:
    # what the kernel sees of a `KnowledgeBase` during one check: the members of `KbReader` and no others --
    # only the lookups it needs (and the trusted normalization and printing it calls), each answer remembered
    # for the whole check, so the environment is immutable while the kernel checks a step, and nothing can be
    # changed through it (doc/kurt-soundness.md section 9). Each member below gives the answer of the same member
    # of the knowledge base, by `_call` (a method) or `_list`, `_frozen`, `_value` (a value): the one place that remembers; a
    # name that is no member is an `AttributeError`, and `tests/test_kernel_env.py` compares every member
    _kb: KbReader
    _memo: dict

    def __init__(self, kb: KbReader) -> None:
        object.__setattr__(self, '_kb', kb)
        object.__setattr__(self, '_memo', {})

    def _call(self, key: str, method: Callable[_P, _R], *args: _P.args, **kwargs: _P.kwargs) -> _R:
        memo = self._memo
        if kwargs:
            return method(*args, **kwargs)       # (the kernel gives none: computed, not remembered)
        entry = (key, *args)
        try:
            hash(entry)
        except TypeError:
            return method(*args, **kwargs)       # an expression as argument: computed, not remembered
        if entry not in memo:
            result = method(*args, **kwargs)
            # a snapshot: a list is handed out as a new list each time, a generator as a new
            # iterator over what it gave, a set as a frozen set
            if isinstance(result, list):
                memo[entry] = (list, tuple(result))
            elif isinstance(result, (set, frozenset)):
                memo[entry] = (frozenset, frozenset(result))
            elif isinstance(result, Iterator):
                memo[entry] = (iter, tuple(result))
            else:
                memo[entry] = (None, result)
        kind, result = memo[entry]
        return result if kind is None or kind is frozenset else kind(result)

    def _list(self, name: str, value: Sequence[T]) -> list[T]:
        memo = self._memo
        if name not in memo:
            memo[name] = tuple(value)
        return list(memo[name])                  # (a copy: the list of the knowledge base can't be changed through it)

    def _frozen(self, name: str, value: AbstractSet[T]) -> frozenset[T]:
        memo = self._memo
        if name not in memo:
            memo[name] = frozenset(value)
        return memo[name]

    def _value(self, name: str, value: T) -> T:
        memo = self._memo
        if name not in memo:
            memo[name] = value
        return memo[name]

    def __setattr__(self, name: str, value) -> None:
        raise AttributeError(f'BUG: the kernel can not change `{name}` of the knowledge base')

    # the symbols
    def is_var(self, s: str) -> bool:
        return self._call('is_var', self._kb.is_var, s)
    def is_bool(self, s: str) -> bool:
        return self._call('is_bool', self._kb.is_bool, s)
    def bool_sig(self, s: str) -> Sequence[int]:
        return self._call('bool_sig', self._kb.bool_sig, s)
    def variable_sorts(self, symbol: str) -> AbstractSet[str]:
        return self._call('variable_sorts', self._kb.variable_sorts, symbol)
    def pos_sort(self, symbol: str, position: int) -> Optional[str]:
        return self._call('pos_sort', self._kb.pos_sort, symbol, position)
    def pos_sorts(self, symbol: str, position: int) -> frozenset[str]:
        return self._call('pos_sorts', self._kb.pos_sorts, symbol, position)
    def all_subsorts(self) -> frozenset[tuple[str, str]]:
        return self._call('all_subsorts', self._kb.all_subsorts)
    def generalized_sorts(self, symbol: str) -> frozenset[str]:
        return self._call('generalized_sorts', self._kb.generalized_sorts, symbol)
    def binder_sorts(self, node: Expr) -> frozenset[str]:
        return self._call('binder_sorts', self._kb.binder_sorts, node)
    def is_bindop(self, s: str) -> bool:
        return self._call('is_bindop', self._kb.is_bindop, s)
    def is_const(self, s: str) -> bool:
        return self._call('is_const', self._kb.is_const, s)
    def is_known(self, s: str) -> bool:
        return self._call('is_known', self._kb.is_known, s)
    def is_used(self, s: str) -> bool:
        return self._call('is_used', self._kb.is_used, s)
    def is_fixed_var(self, s: str) -> bool:
        return self._call('is_fixed_var', self._kb.is_fixed_var, s)
    def is_vocabulary_symbol(self, s: str) -> bool:
        return self._call('is_vocabulary_symbol', self._kb.is_vocabulary_symbol, s)
    def get_arity(self, fun: str) -> int:
        return self._call('get_arity', self._kb.get_arity, fun)
    def is_flat(self, s: str) -> bool:
        return self._call('is_flat', self._kb.is_flat, s)
    def is_sym(self, s: str) -> bool:
        return self._call('is_sym', self._kb.is_sym, s)
    def all_flat(self) -> Iterator[str]:
        return self._call('all_flat', self._kb.all_flat)
    def get_builtins(self, symbol: str) -> Sequence[str]:
        return self._call('get_builtins', self._kb.get_builtins, symbol)
    def has_role(self, symbol: object, role: str) -> bool:
        return self._call('has_role', self._kb.has_role, symbol, role)
    def role_symbol(self, role: str) -> Optional[str]:
        return self._call('role_symbol', self._kb.role_symbol, role)
    def calculate(self, e: Expr) -> Expr:
        return self._call('calculate', self._kb.calculate, e)
    def is_operator(self, s: str) -> bool:
        return self._call('is_operator', self._kb.is_operator, s)
    def is_infix(self, s: str) -> bool:
        return self._call('is_infix', self._kb.is_infix, s)
    def is_prefix(self, s: str) -> bool:
        return self._call('is_prefix', self._kb.is_prefix, s)
    def is_postfix(self, s: str) -> bool:
        return self._call('is_postfix', self._kb.is_postfix, s)
    def is_bracket_placeholder(self, s: str) -> bool:
        return self._call('is_bracket_placeholder', self._kb.is_bracket_placeholder, s)
    # the facts, and how the block was opened
    def all_theory(self) -> Iterator[Formula]:
        return self._call('all_theory', self._kb.all_theory)
    @property
    def theory(self) -> Sequence[Formula]:
        return self._list('theory', self._kb.theory)
    @property
    def const(self) -> AbstractSet[str]:
        return self._frozen('const', self._kb.const)
    @property
    def mode_str(self) -> str:
        return self._value('mode_str', self._kb.mode_str)
    @property
    def mode_args(self) -> Sequence[Expr]:
        return self._list('mode_args', self._kb.mode_args)
    @property
    def let_names(self) -> Sequence[str]:
        return self._list('let_names', self._kb.let_names)
    @property
    def fixed_vars(self) -> AbstractSet[str]:
        return self._frozen('fixed_vars', self._kb.fixed_vars)
    @property
    def pick_source(self) -> Optional[Formula]:
        return self._value('pick_source', self._kb.pick_source)
    @property
    def pick_fact(self) -> Optional[Formula]:
        return self._value('pick_fact', self._kb.pick_fact)
    # how expressions are printed (in a message)
    @property
    def format(self) -> Format:
        return self._value('format', self._kb.format)
    @property
    def calc(self) -> bool:
        return self._value('calc', self._kb.calc)
```

`KbReader` is the whole interface between the kernel and the state of Kurt: which symbols are
variables, statement places, binders, constants; their arities, `flat` and `sym`; the roles of symbols
(which symbol is the universal quantifier, the negation); the calculator; the facts
(`all_theory`, `theory`), the block's constants and how it was opened (`mode_str`, `mode_args`,
`let_names`, `pick_source`, `pick_fact`); and how expressions are printed, for messages. The
`KernelEnv` has exactly these members, and each one only gives the answer of the same member of
the knowledge base, through the one place that remembers it (`_call` for a method, `_list`,
`_frozen`, `_value` for a value). A list is handed out as a new list each time, a set as a frozen
set, a generator as a new iterator over what it gave: the kernel can't change the knowledge base by
changing an answer. A name that is no member is an `AttributeError`.
`tests/test_kernel_boundary.py` checks that the kernel calls no search code;
`tests/test_kernel_env.py` that the view is read-only, that its answers stay fixed, that every
member answers as the knowledge base does, and that each forwards to its own.

<!-- cite: def k_env -->
```python
def k_env(kb: KbReader) -> KbReader:
    return kb if isinstance(kb, KernelEnv) else KernelEnv(kb)
```

Inside the kernel, "this is wrong" is an exception of its own, turned into the verdict at the end
of `kernel_verify` (§4.7):

<!-- cite: class KernelReject -->
```python
class KernelReject(Exception):
    pass
```

## 4. The checker: `kernel_verify`

`kernel_verify` returns `None` when the certificate proves its goal, otherwise a sentence that
says what is wrong (the text of the `KernelError`). It begins by taking the read-only view, by
sending the block rules to `kernel_verify_block` (§6), and by normalizing the goal: `flat`, `sym`
and the calculator, the same `normalize_expr` that every line goes through (§9).

<!-- cite: kernel_verify :: def kernel_verify ... match cert.kind: -->
```python
def kernel_verify(cert: Certificate, kb: KbReader) -> Optional[str]:
    # `None` if the certificate proves its goal, otherwise what is wrong
    kb = k_env(kb)          # read-only, for this check
    try:
        if cert.block is not None:
            return kernel_verify_block(cert)
        goal = normalize_expr(cert.goal, kb)
        match cert.kind:
```

### 4.1 The simple kinds: `todo`, `true`, `calc`

A `todo` is admitted and reported as such; nothing to check. `true` must be `true`. A `calc` step
holds when the comparison holds numerically, as written or after computing
(`numeric_comparison_holds`, `calculate_normalized`: §9).

<!-- cite: kernel_verify :: case 'todo': ... return None if holds else 'the comparison does not hold' -->
```python
case 'todo':
    return None                 # admitted, and reported as a `todo`
case 'top':
    return None if isinstance(cert.goal, Token) and cert.goal.value == TRUE_SYMBOL else 'not `true`'
case 'calc':
    holds = numeric_comparison_holds(cert.goal, kb) or numeric_comparison_holds(calculate_normalized(cert.goal, kb), kb)
    return None if holds else 'the comparison does not hold'
```

### 4.2 A fact that computes to the goal

With `calc on`, a line may be a fact whose numbers compute to the goal's (`x = 2 + 3` from
`x = 5`). The kernel checks that the fact is in the theory and that both compute to the same
expression, compared with its own equality `k_equal` (§5.2).

<!-- cite: kernel_verify :: case 'calc-fact': ... return None if k_equal(calculate_normalized -->
```python
case 'calc-fact':
    assert cert.rule is not None
    if not k_known(cert.rule, kb):
        return 'the fact is not in the theory'
    return None if k_equal(calculate_normalized(cert.rule.expr, kb), calculate_normalized(cert.goal, kb), kb) else 'the fact does not compute to the goal'
```

### 4.3 A `case` block with many alternatives

`case` with n alternatives is a shortcut of the search (`nary_case_elim`): it needs the general
rule of binary disjunction elimination, `(%A ∨ %B) ∧ (%A ⇒ %C) ∧ (%B ⇒ %C) ⇒ %C`, n times. The
kernel recognizes that rule on its own (`k_is_binary_or_elim_rule`, §5.9), and then checks
directly that the first fact is a disjunction, that there is one implication per alternative, and
that each implication goes from its alternative to the goal. Nothing of the rule-instantiation
machinery may be in such a certificate (`cert.expr`, `values`, ...): the shortcut has no values.

<!-- cite: kernel_verify :: case 'case-elim': ... return None -->
```python
case 'case-elim':
    if cert.rule is None or not k_known(cert.rule, kb):
        return 'the binary case-elimination rule is not in the theory'
    if not k_is_binary_or_elim_rule(cert.rule.simplified_expr, kb):
        return 'the supplied rule is not general binary disjunction elimination'
    if cert.expr is not None or cert.form or cert.values or cert.premise_fresh or cert.conclusion_fresh or cert.fact_fresh:
        return 'an n-ary case certificate has unexpected rule-instantiation data'
    if any(not k_known(f, kb) for f in cert.facts):
        return 'a case fact is not in the theory'
    if not cert.facts:
        return 'no disjunction was supplied'
    disjunction = cert.facts[0].simplified_expr
    if not is_disjunction(disjunction, kb) or not isinstance(disjunction, list) or len(disjunction) < 3:
        return 'the first fact is not a disjunction with at least two alternatives'
    branches = disjunction[1:]
    implications = cert.facts[1:]
    if len(implications) != len(branches):
        return 'there is not exactly one implication for each alternative'
    for branch, implication in zip(branches, implications):
        e = implication.simplified_expr
        if not is_implication(e) or not isinstance(e, list):
            return 'a case fact is not an implication'
        if not k_equal(e[1], branch, kb) or not k_equal(e[2], goal, kb):
            return f'the case `{expr_str(e, kb)}` does not prove the goal from its alternative'
    return None
```

### 4.4 A rule: where it comes from, and what the values may be

Everything else is a `'rule'`. Before any instantiation, the kernel checks the provenance of what
the certificate names. The rule's expression must be the rule's own `simplified_expr` (`is`, the
same object -- not a copy the search may have changed), and the rule and every fact must be in
the theory (`k_known`, §5.6). The variables of the goal (`fixed`) got no value. Only variables
got values. No value is the ellipsis `...`, which marks a pattern in a set and is no term
(`proofs/soundness/ellipsis-is-no-term.kurt`). A value of a variable with a declared sort has
that sort (`k_has_sort`, §5.8). And each value has the kind of its variable (`k_has_kind`,
§5.8): a `%`-variable's value is a formula, a `$`-variable's a term, an operator variable's an
operator -- the search made sure of that alone until 2026-10-16, when a `$x` got a formula
through "iff-subst" (`proofs/soundness/term-variable-takes-no-formula.kurt`,
doc/kurt-soundness.md §8.39), and a `%b` the bare operator `=` (`hole-never-at-an-operator.kurt`,
§8.40).

<!-- cite: kernel_verify :: assert cert.kind == 'rule' ... return f'the value `{expr_str(cert.values[v], kb)}` of `{v}` is not {kind}' -->
```python
assert cert.kind == 'rule' and cert.rule is not None and cert.expr is not None
if cert.expr is not cert.rule.simplified_expr or not k_known(cert.rule, kb):
    return 'the rule is not in the theory'
if any(not k_known(f, kb) for f in cert.facts):
    return 'a fact is not in the theory'
if set(cert.values) & cert.fixed:
    return f'the variables {sorted(set(cert.values) & cert.fixed)} of the goal got a value'
not_variables = sorted(v for v in cert.values if not kb.is_var(v))
if not_variables:
    return f'only variables get values, not {", ".join(f"`{v}`" for v in not_variables)}'
dots = sorted(v for v, value in cert.values.items() if is_ellipsis(value))
if dots:
    return f'the value of `{dots[0]}` is `{ELLIPSIS_SYMBOL}`, which is no term (it marks a pattern in a set)'
bad_sorts = [(v, sort) for v, value in cert.values.items()
             for sort in kb.variable_sorts(v)
             if not k_has_sort(value, sort, kb)]
if bad_sorts:
    v, sort = bad_sorts[0]
    return f'the value of `{v}` does not have its declared sort `{sort}`'
bad_kinds = sorted(v for v, value in cert.values.items() if not k_has_kind(v, value, kb))
if bad_kinds:
    v = bad_kinds[0]
    kind = ('an operator with a statement as its result' if kb.is_bool(v) else 'an operator with a term as its result') if k_is_operator_variable(v, kb) else ('a formula' if kb.is_bool(v) else 'a term')
    return f'the value `{expr_str(cert.values[v], kb)}` of `{v}` is not {kind}'
```

### 4.5 The goal is an instance of a fact

With `form == 'fact'` there is no premise, so no fresh names and no facts may be present. The
instance of the rule under the values (`k_instance`: fill in, evaluate `sub`, normalize -- §5.5)
must be the goal, up to the names of bound variables and the order of `sym` arguments (`k_equal`).

`deps` says which schema variables of the rule may take a value that contains a bound variable:
for a postulated rule (`use`, `def`, `todo`), a term variable `$T` that stands as the whole body of
a binder over `x` may be instantiated with a term in `x` -- the body of `∀ x $T` is "a formula
about x" (`k_dependencies`, §5.4). A derived theorem has no such variables.

<!-- cite: kernel_verify :: deps = k_rule_dependencies(cert.expr, cert.rule, kb) ... return None if k_equal(instance, goal, kb) else f'the instance -->
```python
deps = k_rule_dependencies(cert.expr, cert.rule, kb)
relativizable = k_parametric_binders(cert.expr, kb)
mixed = k_poly_sorts(cert.expr, cert.values, kb, k_stripped_names(cert, kb))
if len(mixed) > 1:
    return f'the polymorphic binders of the rule range over different sorts {sorted(sorted(m) for m in mixed)}: one sort per use'
if cert.form == 'fact':
    if cert.premise_fresh or cert.conclusion_fresh or cert.facts:
        return 'a fact has no premise'
    instance = k_instance(cert.expr, cert.values, deps, kb, relativizable)
    return None if k_equal(instance, goal, kb) else f'the instance `{expr_str(instance, kb)}` is not the goal'
```

### 4.6 The goal follows from a rule with a premise

With `form == 'impl'` the rule is an implication `premise ⇒ conclusion`. A premise may begin with
`∀`s (the rule "forall-intro" of logic.kurt has the premise `∀ x P(x)`): the search removed them
and replaced their variables by fresh ones, which stand for anything, and a fact `P(c)` matches
the body only if `c` is such a fresh variable (§4.7). The conclusion may begin with `∀`s too.
`k_strip` removes the same `∀`s with the same fresh names; for the premise's `∀`s it renames in
the conclusion as well, since a `∀` of the premise may scope over variables that also occur in
the conclusion of the rule as stored.

The fresh variables are the eigenvariables of the step, and four checks keep them honest. Each
name is used once. The names are ones that only the search makes (`$$07`, `%%07`) and not a
variable fixed by a block (`x` of `assume R(x)`): a fixed variable is "this one", and reading it
as "any one" would make a universal out of an instance. They occur neither in the goal nor in a
cited fact. They got no value, and no term variable of the rule got a value that depends
on them: `∀ y P(y) ⇒ Q($a)` may not conclude `Q(y)` for the particular `y` of some fact.

<!-- cite: kernel_verify :: if cert.form != 'impl' ... return f'the value of `{v}` depends on the fresh variables -->
```python
if cert.form != 'impl' or not is_implication(cert.expr):
    return f'unknown form `{cert.form}`'
assert isinstance(cert.expr, list)
premise, conclusion = k_strip(cert.expr[1], cert.premise_fresh, kb, cert.expr[2])
assert conclusion is not None
conclusion, _ = k_strip(conclusion, cert.conclusion_fresh, kb)
# the fresh variables of the premise's `∀`s stand for anything: no value, and no variable
# of the rule (except a statement variable, see `k_instantiate`) may depend on them
eigen = set(cert.premise_fresh).union(*cert.fact_fresh)
# ... and they are fresh: names that only the search makes (`new_var_name`: `$$07`, `%%07`),
# each once, in neither the goal nor a cited fact -- not a constant, not a variable fixed
# by a block (`x` of `assume R(x)`), which would make "for all" out of "for this one"
named = list(cert.premise_fresh) + [v for names in cert.fact_fresh for v in names]
if len(named) != len(eigen):
    return 'a fresh variable of a `∀` premise is named twice'
stale = sorted(v for v in eigen if not (v.startswith('$$') or v.startswith('%%')) or kb.is_fixed_var(v))
if stale:
    return f'the variables {stale} of a `∀` premise are not fresh'
seen = {t.value for e in [goal] + [f.simplified_expr for f in cert.facts] for t in get_token_set(e)}
if eigen & seen:
    return f'the fresh variables {sorted(eigen & seen)} of a `∀` premise occur in the goal or a fact'
valued = sorted(eigen & set(cert.values))
# ... except a polymorphic one (`$$x`, todo 35) that stands for the fresh variable of a binder over a sort: the
# rule's own binder `∀ $$x`, matched with the goal's binder over `real`, is that binder (`binder_target`) -- a
# variable that only the search makes, in no fact and not fixed, never a term of the goal
def made_by_the_search(v: str) -> bool:
    if not k_is_poly_variable(v):
        return False
    value = cert.values[v]
    return (isinstance(value, Token) and value.label == 'SYMBOL'
            and isinstance(value.value, str) and value.value.startswith('$$')
            and not kb.is_fixed_var(value.value) and value.value not in seen)
not_renamed = [v for v in valued if not made_by_the_search(v)]
if not_renamed:
    return f'the fresh variables {not_renamed} of a `∀` premise got a value'
rule_vars = {t.value for t in get_token_set(cert.expr) if isinstance(t.value, str) and kb.is_var(t.value) and not kb.is_bool(t.value)}
for v in rule_vars:
    if v in cert.values and k_free(cert.values[v], kb) & eigen:
        return f'the value of `{v}` depends on the fresh variables {sorted(k_free(cert.values[v], kb) & eigen)} of a `∀` premise'
```

One exception to "no value", for a polymorphic variable (`$$x`, todo 35): the premise `∀ $$x (%A ⇔
%B)` of "forall-iff" is stripped to a fresh variable, and the conclusion `∀ $$x %A ⇔ ∀ $$x %B` has the
same variable as its binder. Matched with the goal's binder over `real`, the variable stands for a
fresh variable of that sort (the search gives it that value). This is a rename of a bound
variable, not a term, so the kernel accepts it only if the fresh variable is polymorphic, the
value is a variable that only the search makes (`$$07`), not fixed, in no fact and not in the
goal; a value that is a term (`∀ x` instantiated with `3`) is still refused. The conclusion's
binders are read as polymorphic ones for that (`k_parametric_binders(conclusion)`).

Then the instance of the conclusion must be the goal:

<!-- cite: kernel_verify :: instance = k_instance(conclusion, cert.values, deps, kb, relativizable | k_parametric_binders(conclusion, kb)) ... return f'the instance `{expr_str(instance, kb)}` of the conclusion is not the goal' -->
```python
instance = k_instance(conclusion, cert.values, deps, kb, relativizable | k_parametric_binders(conclusion, kb))
if not k_equal(instance, goal, kb):
    return f'the instance `{expr_str(instance, kb)}` of the conclusion is not the goal'
```

### 4.7 The premise is covered by the facts

The instance of the premise must follow from the instances of the facts. `covered` says when a
part of the premise does: it is equal to a fact; or it is a `∀` whose body, with one of the
recorded fresh names (`fact_fresh`), is covered -- the fact `P(c)` with `c` fresh covers `∀ x
P(x)`, which is how a universal premise is discharged by a generic fact; or it is a conjunction of
covered parts. `covered_all` handles a conjunction whose parts are covered *together* by one fact
that is itself a conjunction: `%A ∧ ¬%A` with `%A := p ∧ q` flattens to `p ∧ q ∧ ¬(p ∧ q)`, and the
fact `p ∧ q` covers two of the three conjuncts at once. The guard `not any(r is first for r in
remaining)` makes sure such a fact consumed the first part, so the recursion makes progress.
Each strip of fresh names is used at most once (`strips[:i] + strips[i+1:]`).

<!-- cite: kernel_verify :: facts = [k_instance(f.simplified_expr ... return str(e) -->
```python
    facts = [k_instance(f.simplified_expr, cert.values, k_rule_dependencies(f.simplified_expr, f, kb), kb,
                        k_parametric_binders(f.simplified_expr, kb)) for f in cert.facts]
    def covered(part: Expr, strips: list[tuple[str, ...]]) -> bool:
        # `part` of the premise is an instance of a fact, or a `∀` whose body is (with one of
        # the recorded fresh variables), or a conjunction of such parts
        if any(k_equal(part, fact, kb) for fact in facts):
            return True
        if is_forall(part, kb) and isinstance(part, list) and isinstance(part[1], Token):
            for i, names in enumerate(strips):
                try:
                    body, _ = k_strip(part, names, kb)
                except KernelReject:
                    continue
                if covered(normalize_expr(body, kb), strips[:i] + strips[i+1:]):
                    return True
        if is_op_expr(part, AND_SYMBOL):
            assert isinstance(part, list)
            return covered_all(part[1:], strips)
        return False
    def covered_all(parts: list[Expr], strips: list[tuple[str, ...]]) -> bool:
        # each of the conjuncts `parts` is covered -- alone, or together with others by a fact
        # that is a conjunction (flattening `%A ∧ ¬%A` with `%A = p ∧ q` gives `p ∧ q ∧ ¬(p ∧ q)`)
        if not parts:
            return True
        first, rest = parts[0], parts[1:]
        if covered(first, strips) and covered_all(rest, strips):
            return True
        for fact in facts:
            if is_op_expr(fact, AND_SYMBOL) and isinstance(fact, list):
                remaining = list(parts)
                for c in fact[1:]:
                    i = next((i for i, r in enumerate(remaining) if k_equal(c, r, kb)), None)
                    if i is None:
                        break
                    del remaining[i]
                else:
                    if len(remaining) < len(parts) and not any(r is first for r in remaining) and covered_all(remaining, strips):
                        return True
        return False
    premise_instance = k_instance(premise, cert.values, deps, kb, relativizable)
    if not covered(premise_instance, list(cert.fact_fresh)):
        return f'the premise `{expr_str(premise_instance, kb)}` does not follow from the facts'
    return None
except KernelReject as e:
    return str(e)
```

The `except KernelReject` at the end turns the exceptions of the helpers (a binder whose variable
can't be read, a capture, an unexpected expression) into the verdict.

## 5. The helpers: the kernel's own reading of expressions

The kernel reads expressions with functions of its own, written again for the kernel, so that a
bug in the search's reading (`unpack_condition`, `equal_expr`, `find_dependent_vars`) is not the
kernel's bug too. They are small and recursive on the shape of an `Expr`: a `Token` (a leaf) or a
list `[op, arg, ...]`. A binder is `[op, cond, *body]`, with `op` a `bindop`, `cond` the condition
that names the bound variable (`x`, `x ∈ A`, or a `sub`), the middle arguments outside the scope
(a `sum`'s range), and only the last one inside.

### 5.1 Which variable a binder binds: `k_bound`

<!-- cite: def k_bound -->
```python
def k_bound(cond: Expr, kb: KbReader) -> str:
    # the kernel's own reading of a binder's condition (not the search's `unpack_condition`): which
    # variable it binds -- the one variable of the condition (a renamed bound variable, or a name
    # unknown on this level, like the constant of a closed `let x ∈ A`), or with several, in a
    # relation like `$a ∈ $G`, the one on its left; `sub $x $v %C` binds `$v`
    match cond:
        case Token(label='SYMBOL', value=v) if isinstance(v, str):
            return v
        case [Token(label='SYMBOL', value=op), _, Token(label='SYMBOL', value=v), _] if op == SUB_SYMBOL and isinstance(v, str):
            return v
        case [Token(label='SYMBOL', value=b), Token(label='SYMBOL', value=v), _] if b == BOUND_SYMBOL and isinstance(v, str):
            return v                       # stored with the condition, as written
    seen: list[str] = []
    def free_name(v: str) -> bool:
        # a variable, a name unknown here, or one known only by a declared sort (`real x` before the
        # closed `let x ...`: no constant any more, no operator) -- with any condition
        return kb.is_var(v) or not kb.is_known(v) or (not kb.is_const(v) and kb.pos_sort(v, 0) is not None
                                                     and not k_takes_arguments(v, kb) and not kb.is_bool(v))
    def collect(e: Expr) -> None:
        match e:
            case Token(label='SYMBOL', value=v) if isinstance(v, str) and free_name(v) and v not in seen:
                seen.append(v)
            case [*children]:
                for c in children:
                    collect(c)
    collect(cond)
    if len(seen) == 1:
        return seen[0]
    match cond:
        case [Token(label='SYMBOL', value=rel), Token(label='SYMBOL', value=v), _] if isinstance(rel, str) and isinstance(v, str) and is_relation(rel, kb) and v in seen:
            return v
    raise KernelReject(f'the condition `{expr_str(cond, kb)}` of a binder has no variable it clearly binds')
```

A plain condition is the variable itself. A `sub $x $v %C` binds `$v`; a condition stored with
its variable (`BOUND_SYMBOL`, from `bound_condition`) says so directly. Otherwise, the one
variable of the condition (a variable, or a name unknown on this level, like the constant of a
closed `let x ∈ A`); with several, in a relation like `$a ∈ $G`, the one on the left. Anything
else is a rejection: a binder the kernel can't read is a step the kernel won't accept.

### 5.2 Equality up to bound names and `sym`: `k_equal`

<!-- cite: def k_equal -->
```python
def k_equal(t1: Expr, t2: Expr, kb: KbReader, bmap1: Optional[dict] = None, bmap2: Optional[dict] = None) -> bool:
    # the kernel's own alpha-equivalence (not the search's `equal_expr`): equal up to the names of
    # bound variables; the arguments of a `sym` operator, and of `=` and `iff`, in any order
    bmap1, bmap2 = bmap1 or {}, bmap2 or {}
    match (t1, t2):
        case (Token(label=l1, value=v1), Token(label=l2, value=v2)):
            if l1 != l2:
                return False
            if v1 in bmap1 or v2 in bmap2:
                return bmap1.get(v1) == v2 and bmap2.get(v2) == v1
            return v1 == v2
        case ([Token(label='SYMBOL', value=op1), cond1, *body1], [Token(label='SYMBOL', value=op2), cond2, *body2]) \
                if isinstance(op1, str) and op1 == op2 and kb.is_bindop(op1) and len(body1) == len(body2):
            b1, b2 = k_bound(cond1, kb), k_bound(cond2, kb)
            if k_binder_sorts(t1, kb) != k_binder_sorts(t2, kb):
                return False    # the bound variables range over the same sort (todo 34)
            m1, m2 = {**bmap1, b1: b2}, {**bmap2, b2: b1}
            if isinstance(cond1, Token) != isinstance(cond2, Token):
                return False
            if not isinstance(cond1, Token) and not k_equal(cond1, cond2, kb, m1, m2):
                return False
            # the middle arguments (a `sum`'s range) are outside the scope, only the last one inside
            return (all(k_equal(a, b, kb, bmap1, bmap2) for a, b in zip(body1[:-1], body2[:-1]))
                    and all(k_equal(a, b, kb, m1, m2) for a, b in zip(body1[-1:], body2[-1:])))
        case ([Token(label='SYMBOL', value=op1), *args1], [Token(label='SYMBOL', value=op2), *args2]) \
                if isinstance(op1, str) and op1 == op2 and len(args1) == len(args2) and len(args1) > 1 and kb.is_sym(op1):
            unused = list(args2)
            for a in args1:
                i = next((i for i, b in enumerate(unused) if k_equal(a, b, kb, bmap1, bmap2)), None)
                if i is None:
                    return False
                del unused[i]
            return True
        case ([*c1], [*c2]) if len(c1) == len(c2):
            return all(k_equal(a, b, kb, bmap1, bmap2) for a, b in zip(c1, c2))
    return False
```

Alpha-equivalence by two maps (`bmap1`, `bmap2`), one in each direction, so that bound names
correspond one-to-one; a free name must be the same on both sides. For a binder, the bound
variables of both sides are mapped to each other for the condition and the last body part, but
not for the middle arguments, which are outside the scope. The arguments of a `sym` operator may
come in any order (each of one side is matched with an unused one of the other); so may those of
`=` and `iff`, because `sym` is declared for them in the theories. Otherwise the lists must agree
element by element. Two binders are equal only if their variables range over the same sort
(`k_binder_sorts`, §5.8): `∀ x` over the numbers is not `∀ x` over everything (todo 34).

### 5.3 Free variables, renaming, stripping `∀`s

<!-- cite: def k_free -->
```python
def k_free(e: Expr, kb: KbReader, bound: frozenset[str] = frozenset()) -> set[str]:
    # the free variables of `e`
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
            return set() if v in bound else {v}
        case Token():
            return set()
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv = k_bound(cond, kb)
            return (set().union(*(k_free(c, kb, bound) for c in body[:-1]))          # outside the scope
                    | set().union(*(k_free(c, kb, bound | {bv}) for c in [cond, *body[-1:]])))
        case [*children]:
            return set().union(*(k_free(c, kb, bound) for c in children)) if children else set()
    raise KernelReject(f'unexpected expression `{e}`')
```

<!-- cite: def k_rename -->
```python
def k_rename(e: Expr, old: str, new: str) -> Expr:
    # rename the variable `old` to the fresh name `new`, everywhere (names are unique)
    if isinstance(e, Token):
        return Token('SYMBOL', new, e.column) if e.value == old else e
    return [k_rename(c, old, new) for c in e]
```

`k_rename` renames everywhere, without regard to binders: the names it is used for are unique
(the fresh names of the search, the bound variables of a rule as stored), so nothing can be
captured by it.

<!-- cite: def k_strip -->
```python
def k_strip(e: Expr, names: tuple[str, ...], kb: KbReader, also: Optional[Expr] = None) -> tuple[Expr, Optional[Expr]]:
    # remove outer `∀`s (without condition) of `e`, one per name, renaming the bound variable to
    # the name -- also in `also` (the conclusion, for the `∀`s of a premise)
    for name in names:
        match e:
            case [Token(label='SYMBOL', value=q), Token(label='SYMBOL', value=bv), body] if kb.has_role(q, 'universal') and isinstance(bv, str):
                e = k_rename(body, bv, name)
                if also is not None:
                    also = k_rename(also, bv, name)
            case _:
                raise KernelReject(f'expected {len(names)} outer universal quantifiers')
    return e, also
```

`k_strip` removes one outer `∀` without a condition per name, renaming the bound variable to that
name, also in `also` (the conclusion, when the premise's `∀`s are stripped). Fewer `∀`s than
names is a rejection: the search claims to have stripped what isn't there.

### 5.4 Which variables may depend on a bound variable: `k_dependencies`

<!-- cite: def k_dependencies -->
```python
def k_dependencies(e: Expr, kb: KbReader) -> dict[str, str]:
    # which term schema variables may contain which bound variable: those that occur as
    # the whole body of a binder over the variable, and otherwise only inside binders over it or
    # `sub`s for it (the same criterion as `find_dependent_vars`, written again for the kernel)
    contexts: dict[str, list[tuple[frozenset[str], Optional[str]]]] = {}
    def note(t: Expr, scopes: frozenset[str], whole: Optional[str]) -> bool:
        if isinstance(t, Token) and isinstance(t.value, str) and t.value.startswith('$') and kb.is_var(t.value) and not kb.is_bool(t.value):
            contexts.setdefault(t.value, []).append((scopes, whole))
            return True
        return False
    def walk(t: Expr, scopes: frozenset[str]) -> None:
        match t:
            case Token():
                note(t, scopes, None)
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), a, A] if op == SUB_SYMBOL and isinstance(x, str):
                walk(a, scopes)
                if not note(A, scopes | {x}, None):
                    walk(A, scopes | {x})
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                bv = k_bound(cond, kb)
                walk(cond, scopes)
                for c in body[:-1]:
                    walk(c, scopes)
                if body and not note(body[-1], scopes | {bv}, bv):
                    walk(body[-1], scopes | {bv})
            case [*children]:
                for c in children:
                    walk(c, scopes)
    walk(e, frozenset())
    result = {}
    for v, cs in contexts.items():
        wholes = {whole for _, whole in cs if whole is not None}
        if len(wholes) == 1:
            b = wholes.pop()
            if all(b in scopes for scopes, _ in cs):
                result[v] = b
    return result
```

<!-- cite: def k_rule_dependencies -->
```python
def k_rule_dependencies(e: Expr, f: Formula, kb: KbReader) -> dict[str, str]:
    # the dependent variables of a rule: only of a postulated one, and not those of its outer `∀`s
    # (see `POSTULATED`; `e` is `f`'s `simplified_expr`, or one direction of it, an `iff`)
    if f.keyword not in ('use', 'def', 'todo'):
        return {}
    return {v: b for v, b in k_dependencies(e, kb).items() if v not in f.first_order}
```

The criterion of `find_dependent_vars`, written again: a term schema variable `$T` may
contain a bound variable `x` when it occurs as the whole body of a binder over `x` (`∀ x $T`), and
everywhere else only inside binders over `x` or `sub`s for `x`. That makes `$T` "a formula about
x", which its value may be. Only postulated rules (`use`, `def`, `todo`) have such variables, and
not the variables of their outer `∀`s that are written out (`first_order`): those were treated as
fixed terms by the proof. A derived theorem's proof treated its variables as fixed, so none of
them may depend on anything.

### 5.5 Instantiating a rule: `k_instantiate`, `k_replace`, `k_evaluate`, `k_instance`

<!-- cite: def k_instantiate -->
```python
def k_instantiate(e: Expr, values: dict[str, Expr], deps: dict[str, str], kb: KbReader, bound: frozenset[str] = frozenset()) -> Expr:
    # fill in the values of the variables -- without renaming, so a value may contain a variable
    # that is bound where the variable occurs only if that is meant: a statement variable `%A` may (as in
    # "forall-elim"), a term variable `$T` only its own bound variable (see `k_dependencies`)
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and v not in bound and v in values:
            value = values[v]
            captured = k_free(value, kb) & bound
            allowed = bound if kb.is_bool(v) else ({deps[v]} if v in deps else set())
            if not captured <= allowed:
                raise KernelReject(f'the value `{expr_str(value, kb)}` of `{v}` would capture {sorted(captured - allowed)}')
            return deepcopy_expr(value)
        case Token():
            return e
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv = k_bound(cond, kb)
            return [e[0], k_instantiate(cond, values, deps, kb, bound | {bv}),
                    *(k_instantiate(c, values, deps, kb, bound) for c in body[:-1]),          # outside the scope
                    *(k_instantiate(c, values, deps, kb, bound | {bv}) for c in body[-1:])]
        case [*children]:
            return [k_instantiate(c, values, deps, kb, bound) for c in children]
    raise KernelReject(f'unexpected expression `{e}`')
```

The values are filled in *without* renaming. So a value that contains a variable bound at the
place of the occurrence would be captured -- and that is allowed only when it is meant: a statement
variable `%A` may take any value (as in "forall-elim", `∀ x %A ⇒ sub x $t %A`, where `%A` is a formula about
`x`), a term variable `$T` only its own bound variable from `deps`. Everything else is a rejection,
the capture check that the search's `may_capture` makes as well.

<!-- cite: def k_replace -->
```python
def k_replace(A: Expr, x: str, t: Expr, kb: KbReader) -> Expr:
    # `A` with `t` for the free occurrences of `x`, renaming a binder that would capture `t`
    match A:
        case Token(label='SYMBOL', value=v) if v == x:
            return deepcopy_expr(t)
        case Token():
            return A
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv = k_bound(cond, kb)
            middle = [k_replace(c, x, t, kb) for c in body[:-1]]       # outside the scope of `bv`
            if bv == x:
                return [A[0], cond, *middle, *body[-1:]]
            if bv in k_free(t, kb):
                fresh = new_bool_var_name(bv) if kb.is_bool(bv) else new_var_name(bv)
                cond, inner = k_rename(cond, bv, fresh), [k_rename(c, bv, fresh) for c in body[-1:]]
            else:
                inner = body[-1:]
            return [A[0], k_replace(cond, x, t, kb), *middle, *(k_replace(c, x, t, kb) for c in inner)]
        case [*children]:
            return [k_replace(c, x, t, kb) for c in children]
    raise KernelReject(f'unexpected expression `{A}`')
```

`k_replace` is capture-avoiding substitution, used to evaluate `sub`: `A` with `t` for the free
`x`; a binder over `x` stops the substitution in its scope (but not in the middle arguments); a
binder whose variable occurs free in `t` is renamed to a fresh name first.

<!-- cite: def k_evaluate -->
```python
def k_evaluate(e: Expr, kb: KbReader) -> Expr:
    # evaluate the `sub`s, innermost first; a `sub` with a still unknown `%A` stays
    match e:
        case Token():
            return e
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x) as tx, t, A] if op == SUB_SYMBOL and isinstance(x, str):
            t, A = k_evaluate(t, kb), k_evaluate(A, kb)
            if is_bool_var_token(A, kb) and A != tx:
                return [e[0], tx, t, A]
            if not kb.is_bool(x):
                for sort in kb.variable_sorts(x):
                    if not k_has_sort(t, sort, kb):
                        raise KernelReject(f'`{expr_str(t, kb)}` does not have the sort `{sort}` of `{x}`, which it replaces')
            return k_replace(A, x, t, kb)
        case [Token(label='SYMBOL', value=op), cond, *_] if isinstance(op, str) and kb.is_bindop(op) and is_sub(cond):
            # a binder with any condition, `∀ (sub $x $v C)`: `C` must not contain `$v` itself
            assert isinstance(cond, list)
            v = cond[2]
            assert isinstance(v, Token) and isinstance(v.value, str)
            if v.value in k_free(cond[3], kb):
                raise KernelReject(f'the condition `{expr_str(cond[3], kb)}` contains its bound variable `{v.value}`')
            new_cond = k_evaluate(cond, kb)
            if isinstance(new_cond, list) and not is_sub(new_cond):
                new_cond = bound_condition(v.value, new_cond)    # it binds `$v`, stored with the condition
            return [e[0], new_cond, *(k_evaluate(c, kb) for c in e[2:])]
        case [*children]:
            return [k_evaluate(c, kb) for c in children]
    raise KernelReject(f'unexpected expression `{e}`')
```

`k_evaluate` evaluates the `sub`s of an instantiated rule, innermost first. A `sub` whose body is
still a statement variable without a value stays as it is (the search may have left `%A` open). A
binder with a condition that is a `sub` (`∀ (sub $x $v C)`, the general form of a conditioned
quantifier) must not have its own bound variable in `C`; after evaluating, the condition is stored
with its variable (`bound_condition`), so that `k_bound` reads it unambiguously later. The value
put in for the variable of a `sub` must have the variable's sort (`k_has_sort`): with `∀ x` over
the numbers, "forall-elim" gives nothing about a set (todo 34).

<!-- cite: def k_instance -->
```python
def k_instance(e: Expr, values: dict[str, Expr], deps: dict[str, str], kb: KbReader,
               relativizable: 'set[str] | frozenset[str]' = frozenset()) -> Expr:
    # a bound variable of the rule with a variable as its value: every occurrence of it is that
    # variable. With another sort than its own (todo 34) only one of `relativizable`
    # (`k_parametric_binders`), and only a smaller sort: the binder over all objects (or over
    # the sets) used for one over the numbers
    binders = k_binder_variables(e, kb) if values else set()
    for v, value in values.items():
        if v in binders and isinstance(value, Token) and value.label == 'SYMBOL' and isinstance(value.value, str) \
                and value.value != v and kb.is_var(value.value):
            own, new = set(kb.variable_sorts(v)), set(kb.variable_sorts(value.value))
            if own != new:
                if v not in relativizable:
                    raise KernelReject(f'the bound variable `{v}` of the rule occurs in a body, it can not range over another sort than its own')
                if not new or any(not any(k_sort_fits(n, o, kb) for n in new) for o in own):
                    raise KernelReject(f'the bound variable `{v}` of the rule has the sort {sorted(own) or "of everything"}, its value `{value.value}` {sorted(new) or "of everything"}')
            e = k_rename(e, v, value.value)       # (every occurrence, bound or free)
            deps = {d: (value.value if b == v else b) for d, b in deps.items()}   # (a `$T` may depend on it as before)
    return normalize_expr(k_evaluate(k_instantiate(e, values, deps, kb), kb), kb)
```

Fill in, evaluate, normalize -- the kernel's instance of an expression under the values. Before
that, a bound variable of the rule that has a variable as its value is that variable everywhere
(`k_rename`, bound and free occurrences alike): this is how a rule written without sorts
(logic.kurt's `∀ $x %A`) is used for a binder over the numbers (todo 34) -- the search gives the
rule's bound variable the binder's variable as its value (`binder_target`). The kernel allows it
only for a variable of another sort if the variable is in `relativizable` -- the rule's bound
variables that the author wrote `$$x` (polymorphic, todo 35) and that occur nowhere but where they
are bound, in `sub`s and as a side of `=` (`k_parametric_binders`), so that the rule says nothing
about their range and each `sub` checks what is put in -- and only for a smaller sort (not the
sort of all objects for one over the numbers). "extensionality", `∀ $c ($c ∈ $a ⇔ $c ∈ $b)`
with `$c` in the body, is never used so (and `$$c` there is refused where the rule is stated): for the numbers alone it would give
`∅ = {∅}` (doc/kurt-soundness.md §8.41). A `$T` that may depend on the renamed variable may
depend on the new one (`deps`).

<!-- cite: def k_binder_variables -->
```python
def k_binder_variables(e: Expr, kb: KbReader) -> set[str]:
    # the variables that a binder of `e` binds
    match e:
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            return {k_bound(cond, kb)} | set().union(*(k_binder_variables(c, kb) for c in [cond, *body]))
        case [*children]:
            return set().union(*(k_binder_variables(c, kb) for c in children)) if children else set()
    return set()
```

A polymorphic variable is one the author wrote `$$x` -- the name is the mark: a letter after the `$$`
(an internal name is `$$07`, digits only) -- or one the search renamed from it (`run_state.poly_variables`,
which only ever gets a name whose origin was written so). The kernel reads the mark; it never
makes one, and a mark is only a permission: `k_parametric_binders` below checks where the variable
occurs.

<!-- cite: def k_is_poly_variable -->
```python
def k_is_poly_variable(v: str) -> bool:
    # a variable the author wrote `$$x` (a letter after the `$$`: an internal name is `$$07`), or one
    # renamed from it: the name is the mark, `run_state.poly_variables` the renamed ones
    return (v.startswith('$$') and len(v) > 2 and not v[2:].isdigit()) or v in run_state.poly_variables
```

<!-- cite: def k_parametric_binders -->
```python
def k_parametric_binders(rule: Expr, kb: KbReader) -> set[str]:
    # the kernel's reading of which bound variables of a rule may range over a smaller sort than
    # their own (todo 34, 35): those the author wrote `$$x` (polymorphic) -- and that occur only
    # where they are bound (the binder, its condition), as the variable of a `sub` and as a side of
    # `=`: the rule then says nothing about their range, the `sub`s check what is put in
    # (`k_evaluate`). Not one in a body, `∀ $$c ($$c ∈ $a ⇔ $$c ∈ $b)` of "extensionality": for the
    # numbers alone, it would give `∅ = {∅}` (doc/kurt-soundness.md)
    bound: set[str] = set()
    bad: set[str] = set()
    def walk(e: Expr, where_ok: frozenset[str]) -> None:
        match e:
            case Token(label='SYMBOL', value=v) if isinstance(v, str):
                if v not in where_ok:
                    bad.add(v)
            case [Token(label='SYMBOL', value='='), a, b]:
                for side in (a, b):
                    if not isinstance(side, Token):
                        walk(side, where_ok)      # (a variable as a side of `=`: the identity, the same in every sort)
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), a, A] if op == SUB_SYMBOL and isinstance(x, str):
                if not isinstance(a, Token):
                    walk(a, where_ok)     # (a variable as the value: `k_evaluate` checks its sort)
                walk(A, where_ok)
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                bv = k_bound(cond, kb)
                bound.add(bv)
                walk(cond, where_ok | {bv})
                for c in body:
                    walk(c, where_ok)
            case [*children]:
                for c in children:
                    walk(c, where_ok)
    walk(rule, frozenset())
    return {v for v in bound if k_is_poly_variable(v)} - bad      # (marked `$$x` by the author, and only where it may be)
```

One sort per use (doc/kurt-spec.md §2.3): all polymorphic binders of one step range over the same
sort, otherwise "existsunique-intro" with `∃! $$x` over `any` and `∀ $$y` over `real` gives `∃!`
among all objects from uniqueness among the numbers (doc/kurt-soundness.md §8.42). `k_poly_sorts`
reads the sort of each `$$` binder of the rule: the sort of its value (the fresh variable of a binder
over a sort), else its own (none: `any`). An outer `∀` the certificate strips is read by its fresh
name (`k_stripped_names`): one of the premise by that name's value or its own sort, one of the
conclusion only by a value. The variable of a `sub` is no binder over a sort and is not counted.
Two sorts reject the step (§4.5).

<!-- cite: def k_stripped_names -->
```python
def k_stripped_names(cert: Certificate, kb: KbReader) -> tuple[dict[str, str], dict[str, str]]:
    # the bound variables of the outer `∀`s of a rule's premise and of its conclusion that the
    # certificate strips, with the fresh name of each (`k_strip`)
    found: list[dict[str, str]] = [{}, {}]
    if cert.form == 'impl' and cert.expr is not None and is_implication(cert.expr):
        assert isinstance(cert.expr, list)
        for names, part, fresh in ((found[0], cert.expr[1], cert.premise_fresh), (found[1], cert.expr[2], cert.conclusion_fresh)):
            for name in fresh:
                match part:
                    case [Token(label='SYMBOL', value=q), Token(label='SYMBOL', value=bv), body] if kb.has_role(q, 'universal') and isinstance(bv, str):
                        names[bv] = name
                        part = body
                    case _:
                        break
    return found[0], found[1]
```

<!-- cite: def k_poly_sorts -->
```python
def k_poly_sorts(rule: Expr, values: dict[str, Expr], kb: KbReader,
                 stripped: tuple[dict[str, str], dict[str, str]] = ({}, {})) -> set[frozenset[str]]:
    # the sorts the polymorphic binders (`$$x`) of a rule range over in one use: a binder's value
    # (the fresh variable of a binder over a sort) or its own (none: `any`); a stripped outer `∀`
    # of the premise by its fresh name (its value or its own sort), one of the conclusion only by
    # a value. One use has one sort (doc/kurt-spec.md): `∃! $$x` over `any` and its `∀ $$y` over
    # `real` are two
    # (not the variable of a `sub`: the hole of a substitution ranges over no sort)
    def binders(e: Expr) -> set[str]:
        match e:
            case [Token(label='SYMBOL', value=op), _, _, body] if op == SUB_SYMBOL:
                return binders(body)
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                return {k_bound(cond, kb)} | set().union(*(binders(c) for c in [cond, *body]))
            case [*children]:
                return set().union(*(binders(c) for c in children)) if children else set()
        return set()
    found: set[frozenset[str]] = set()
    for v in binders(rule):
        if not k_is_poly_variable(v):
            continue
        premise_stripped, conclusion_stripped = stripped
        name = premise_stripped.get(v, conclusion_stripped.get(v, v))
        value = values.get(name)
        if isinstance(value, Token) and value.label == 'SYMBOL' and isinstance(value.value, str) and kb.is_var(value.value):
            found.add(frozenset(kb.variable_sorts(value.value)) or frozenset({'any'}))
        elif value is None and v not in conclusion_stripped:
            found.add(frozenset(kb.variable_sorts(name)) or frozenset({'any'}))     # (no sort: over all objects)
    return found
```

### 5.6 Provenance: `k_known`

<!-- cite: def k_known -->
```python
def k_known(f: Formula, kb: KbReader) -> bool:
    # whether `f` is a formula of the theory (or one direction of an `iff` of the theory)
    for g in kb.all_theory():
        if g is f:
            return True
        if f.direction_of is not None and g.id == f.id and g.simplified_expr is f.direction_of and is_iff(f.direction_of, kb):
            L, R = f.direction_of[1], f.direction_of[2]
            e = f.simplified_expr
            return is_implication(e) and ((e[1] is L and e[2] is R) or (e[1] is R and e[2] is L))
    return False
```

A formula is known when it *is* an object of the theory, at any level (`all_theory`), or one
direction of an `iff` of the theory: `direction_of` points at the stored `iff`, and the direction
must be one of its two, made of the very same sub-objects. Identity, not equality: the kernel
doesn't accept a rule that merely looks like one of the theory.

### 5.7 Constants: `k_constants`

<!-- cite: def k_constants -->
```python
def k_constants(e: Expr, kb: KbReader, bound: frozenset[str] = frozenset()) -> set[str]:
    # the symbols of `e` that are not variables and not bound
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str):
            return set() if v in bound or kb.is_var(v) else {v}
        case Token():
            return set()
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv = k_bound(cond, kb)
            return ({op} | set().union(*(k_constants(c, kb, bound) for c in body[:-1]))      # outside the scope
                    | set().union(*(k_constants(c, kb, bound | {bv}) for c in [cond, *body[-1:]])))
        case [*children]:
            return set().union(*(k_constants(c, kb, bound) for c in children)) if children else set()
    raise KernelReject(f'unexpected expression `{e}`')
```

The symbols that are not variables and not bound -- used when a block closes, to see that no
constant of the block escapes (§6).

### 5.8 Sorts and kinds: `k_has_sort`, `k_is_statement`

<!-- cite: def k_has_sort -->
```python
def k_has_sort(e: Expr, sort: str, kb: KbReader) -> bool:
    """Kernel-side check of an optional result sort, independent of the search type checker:
    the value's sort is `sort` or a subsort of it (todo 34). Every value fits `any`, and a value
    without a sort only `any` (todo 35)."""
    if sort == 'any':
        return True
    found = k_value_sorts(e, kb)
    return any(k_sort_fits(f, sort, kb) for f in found)
```

A value for a variable of a sort (`sort nat` and `nat a, b`, or one Kurt inferred, doc/kurt-ref.md
§5.2; `variable_sorts`, `pos_sort`) must have that sort or a smaller one -- `sort set real` makes
`real ⊂ set`, a number fits where a set is required; a value without a sort fits none. The value's sort is read by the kernel itself
(`k_value_sorts`): a symbol by its own sorts, a number by the sort of the number literals, an
application by the result sort of its operator (of a variable operator, by the variable's), a
`sub` by its body; and the subsorts are followed upwards by the kernel's own walk over the pairs
the theories declared (`k_sort_fits`), not by the search's remembered closure.

<!-- cite: def k_sort_fits -->
```python
def k_sort_fits(value_sort: str, required: str, kb: KbReader) -> bool:
    # the kernel's own reading of the subsorts: `value_sort` is `required` or below it, by the
    # pairs the theory declared (`sort set real`), followed upwards
    if value_sort == required or (required == 'any' and value_sort != 'prop'):
        return True
    pairs = kb.all_subsorts()
    seen = {value_sort}
    todo = [value_sort]
    while todo:
        s = todo.pop()
        for sub, sup in pairs:
            if sub == s and sup not in seen:
                if sup == required:
                    return True
                seen.add(sup)
                todo.append(sup)
    return False
```

<!-- cite: def k_value_sorts -->
```python
def k_value_sorts(e: Expr, kb: KbReader) -> set[str]:
    # the kernel's reading of the sorts of a value: a symbol's or variable's, the result of its operator
    match e:
        case Token(label='SYMBOL', value=value) if isinstance(value, str):
            return set(kb.variable_sorts(value))
        case Token(label='INT' | 'FLOAT'):
            sort = kb.pos_sort(NUMBERS_KEY, 0)
            return {sort} if sort is not None else set()
        case [Token(label='SYMBOL', value=op), _, _, body] if op == SUB_SYMBOL:
            return k_value_sorts(body, kb)
        case [Token(label='SYMBOL', value=op), *args] if isinstance(op, str):
            if kb.is_var(op):
                return set(kb.variable_sorts(op))
            profiles = kb.pos_sorts(op, 0)
            if len(profiles) > 1:
                return {k_overload_result(op, args, profiles, kb)}
            sort = kb.pos_sort(op, 0)
            return {sort} if sort is not None else set()
    return set()
```

An operator with several signatures (overloading, doc/kurt-kernel.md §8.5) has the sort of its
*least* signature that every argument at a sorted place fits (`k_overload_result`); with no such
signature, the greatest. The signatures of a symbol are one chain on the same places (checked where
they are declared, `overload_problem`), so there is always a smallest of the applicable ones. A larger
sort claims less, so the fallback can only reject a step, never accept a wrong one.

<!-- cite: def k_overload_result -->
```python
def k_overload_result(op: str, args: list[Expr], profiles: frozenset[str], kb: KbReader) -> str:
    # the kernel's reading of the sort of `op args` for an overloaded `op` (decision 19 of dev/todo-sorts.md,
    # doc/kurt-kernel.md §8.5): its profiles are one chain, and the sort is the smallest profile that every
    # argument at a sorted place fits -- else the greatest one (a larger sort only claims less)
    flat = kb.is_flat(op) or kb.is_bracket_placeholder(op)
    given = [k_value_sorts(a, kb) for position, a in enumerate(args, 1) if kb.pos_sorts(op, 1 if flat else position)]
    candidates = [p for p in profiles if all(any(k_sort_fits(found, p, kb) for found in sorts) for sorts in given)]
    if candidates:
        return next((p for p in sorted(candidates) if all(k_sort_fits(p, o, kb) for o in candidates)), sorted(candidates)[0])
    return next((p for p in sorted(profiles) if all(k_sort_fits(o, p, kb) for o in profiles)), sorted(profiles)[0])
```

The sort of a binder's variable (`k_binder_sorts`): of a renamed one, as stored; of one as written
(the result of a closing block, a line before it is stored), or a renamed one stored without a
sort, as the line reads it (`binder_sorts`, the search's reading of a formula -- shared with the
kernel like the normal form, a function of the formula and the declarations). A binder without a
sort -- no declaration, no sorted place, no `default` -- is over all objects, `{any}` (todo 35,
doc/kurt-soundness.md §8.43), inside a formula as at its top. And a binder over the elements
of a set written by its elements (`∀ x ∈ {1, 2}`) ranges over their sort, whatever its variable
was given.

<!-- cite: def k_binder_sorts -->
```python
def k_binder_sorts(node: Expr, kb: KbReader) -> frozenset[str]:
    # the sorts of the variable of a binder: of a renamed one as stored; of one as written, read from
    # its binder like the line was (`binder_node_sorts`, shared like the normal form)
    assert isinstance(node, list)
    bv = k_bound(node[1], kb)
    renamed = bv[:2] in ('$$', '%%') and bv[2:].isdigit()       # (a renamed variable, as stored)
    found = (frozenset(kb.variable_sorts(bv)) if renamed else kb.binder_sorts(node)) - {'any'}   # (over all objects: `{}`, canonical)
    # over the elements of a set whose elements have a sort (`∀ x ∈ Int`, `real ∈ Int`): over that sort
    cond = node[1]
    if isinstance(cond, list) and len(cond) == 3 and isinstance(cond[0], Token) and cond[0].value == BOUND_SYMBOL:
        cond = cond[2]
    match cond:
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=v), container] \
                if v == bv and isinstance(op, str) and CALCULATOR_MEMBERSHIP in kb.get_builtins(op):
            element: Optional[str] = None
            if isinstance(container, list) and len(container) > 1 and isinstance(container[0], Token) and kb.has_role(container[0].value, 'setbrackets'):
                parts = [k_value_sorts(c, kb) for c in container[1:] if not is_ellipsis(c)]
                if parts and all(len(p) == 1 for p in parts):
                    flat = [next(iter(p)) for p in parts]
                    element = next((c for c in flat if all(k_sort_fits(o, c, kb) for o in flat)), None)
            if element is not None and all(k_sort_fits(element, x, kb) for x in found):
                return frozenset({element})
    return found
```

<!-- cite: def k_is_statement -->
```python
def k_is_statement(e: Expr, kb: KbReader, as_operator: bool = False) -> bool:
    # whether `e` is a formula, not a term, as the kernel reads it: a statement variable or symbol
    # that takes no arguments (`%A`, `prop A`, `true`, `false`), an application of an operator
    # with a statement as its result, also a compound one (`(¬¬=) c c`; `<` of the calculator), or a
    # `sub` whose body is one -- the kind a `%`-variable's value has and a `$`-variable's value
    # has not. A bare operator (`=`, `∧`, `prop P` with `arity P 1`) is no formula: only at an
    # operator position (`as_operator`) does it say what its application is
    match e:
        case Token(label='TODO'):
            return True
        case Token(label='SYMBOL', value=v) if isinstance(v, str):
            if not as_operator and k_takes_arguments(v, kb):
                return False
            builtins = kb.get_builtins(v)
            if builtins:
                return all(operation in CALCULATOR_STATEMENT_RESULTS for operation in builtins)
            return kb.is_bool(v)
        case [Token(label='SYMBOL', value=op), _, _, body] if op == SUB_SYMBOL:
            return k_is_statement(body, kb, as_operator)
        case [head, *_]:
            return k_is_statement(head, kb, as_operator=True)
    return False
```

Whether a value is a formula or a term -- the kind of §3.1 of doc/kurt-spec.md, which the kernel
checks for every value (§4.4): a symbol by its own signature (`is_bool`: a `%`-name, a `prop`
symbol, `true`, `false`; a symbol bound to the calculator by its operations, `<` but not `+`), an
application by its operator -- also an operator that is itself an application, `(¬¬P) c c` --,
and a `sub` by its body. A symbol that takes arguments (`k_takes_arguments`: an operator, or a
function symbol with an arity) is a formula only at an operator position (`as_operator`), where
it says what its application is: on its own, `=`, `∧` or a `prop P` with `arity P 2` is no
formula, although its signature gives a statement as its result -- the hole of a `sub` cut at the `=` of
`c = c` made a `%b := =`, and "iff-subst" with "not-not" gave `R (c = c)` from `R ((¬¬(=)) c c)`
(doc/kurt-soundness.md §8.40). It is the kernel's own reading, next to the search's `bool_expr`,
which the unifier asks before it binds a variable (`compatible` in `unify_exprs_with_patterns`,
with `bare_operator_for`).

<!-- cite: def k_takes_arguments -->
```python
def k_takes_arguments(v: str, kb: KbReader) -> bool:
    # an operator (prefix, infix, postfix, brackets) or a function symbol (`arity f 1`)
    return kb.is_operator(v) or kb.get_arity(v) > 0
```

<!-- cite: def k_is_operator_variable -->
```python
def k_is_operator_variable(v: str, kb: KbReader) -> bool:
    # a variable declared as an operator (`var ∘` with `infix ∘`), also by its fresh internal name
    # (`$$07`, whose origin is `∘`)
    return k_takes_arguments(v, kb) or k_takes_arguments(run_state.origin_names.get(v, v), kb)
```

An operator variable (`var ∘` with `infix ∘ 70 70`) is declared as an operator; in a stored formula
it has a fresh internal name (`$$07`), whose origin (`origin_names`, recorded when the name is
made) is the declared one.

<!-- cite: def k_has_kind -->
```python
def k_has_kind(v: str, value: Expr, kb: KbReader) -> bool:
    # the kind check of a value (doc/kurt-spec.md §3.1): a `%`-variable takes a formula; a
    # `$`-variable a term -- no formula, and no bare operator (`=`, `+`, `f`: an operator is no
    # object, decided 2026-10-20); an operator variable (`var ∘`) an operator with its result
    if k_is_operator_variable(v, kb):
        return kb.is_bool(v) == k_is_statement(value, kb, as_operator=True)
    if kb.is_bool(v):
        return k_is_statement(value, kb)
    if isinstance(value, Token) and value.label == 'SYMBOL' and isinstance(value.value, str) and k_is_operator_variable(value.value, kb):
        return False            # (an operator is no object, so no term: only an operator variable takes one)
    return not k_is_statement(value, kb, as_operator=True)
```

The kind check of a value: a `%`-variable takes a formula (`k_is_statement`, so never a bare
operator); a `$`-variable a term -- what is no formula, also read as an operator: `(+)`, the
operation of `group(R, (+), 0, (-))`, is a term, a bare `=` is neither a term nor a formula; an
operator variable takes an operator, or an expression in its place, whose result has the
variable's kind (`∘ := +`, `rel := sim` with a statement as its result).

### 5.9 The binary rule behind an n-ary `case`: `k_is_binary_or_elim_rule`

<!-- cite: def k_is_binary_or_elim_rule -->
```python
def k_is_binary_or_elim_rule(e: Expr, kb: KbReader) -> bool:
    # Independent kernel-side recognition of the general rule that justifies the n-ary shortcut.
    if not is_implication(e) or not isinstance(e, list):
        return False
    premise, conclusion = e[1], e[2]
    if not is_op_expr(premise, AND_SYMBOL) or not isinstance(premise, list) or len(premise) != 4:
        return False
    disjunctions = [part for part in premise[1:]
                    if is_disjunction(part, kb) and isinstance(part, list) and len(part) == 3]
    if len(disjunctions) != 1:
        return False
    disjunction = disjunctions[0]
    branches = disjunction[1:]
    schemas = [*branches, conclusion]
    if not all(is_bool_var_token(v, kb) for v in schemas):
        return False
    if len({v.value for v in schemas if isinstance(v, Token)}) != 3:
        return False
    implications = [part for part in premise[1:] if part is not disjunction]
    return len(implications) == 2 and all(
        any(is_implication(imp) and isinstance(imp, list)
            and k_equal(imp[1], branch, kb) and k_equal(imp[2], conclusion, kb)
            for imp in implications)
        for branch in branches
    )
```

The shape of general disjunction elimination, recognized structurally: a premise that is a
conjunction of exactly three parts, one of them a binary disjunction of two statement variables,
the two others implications from each alternative to the conclusion, with three distinct statement
variables in all.

### 5.10 How a result reads outside the block: `k_reading`, `k_reading_changes`

<!-- cite: def k_reading -->
```python
def k_reading(e: Expr, kb: KbReader) -> Optional[list[str]]:
    # the variables bound by the binders of `e`, in order, as the kernel reads them (`k_bound`) --
    # `None` if a condition can't be read
    match e:
        case Token():
            return []
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            try:
                bv = k_bound(cond, kb)
            except KernelReject:
                return None
            parts = [k_reading(c, kb) for c in [cond, *body]]
            readings = [bv]
            for p in parts:
                if p is None:
                    return None
                readings += p
            return readings
        case [*children]:
            parts = [k_reading(c, kb) for c in children]
            flat: list[str] = []
            for p in parts:
                if p is None:
                    return None
                flat += p
            return flat
    return None
```

<!-- cite: def k_reading_changes -->
```python
def k_reading_changes(block: KbReader, parent: KbReader, result: Expr, last: Expr) -> Optional[str]:
    # whether the result of closing `block` reads differently at the parent than its last line did
    # inside the block (the kernel's own version of `binder_reading_changes`)
    inside = k_reading(last, block)
    outside = k_reading(result, parent)
    if inside is None or outside is None:
        return None     # can't be read at all -- the other checks report that
    if block.mode_str == 'let':
        # each name, and the binders inside its condition (a set-builder)
        # (the name a condition binds is the block's, as the closed `let` stores it, `bound_condition`:
        # in `let w with $a <= w` inside `assume P $a`, `w`, not the fixed `$a`)
        prefix = [v for c, name in zip(block.mode_args, block.let_names) if not is_bool_var_token(c, parent)
                  for v in [k_bound(bound_condition(name, c) if isinstance(c, list) else c, parent)] + (k_reading(c, parent) or [])]
    elif block.mode_str in ('assume', 'case'):
        prefix = k_reading(block.mode_args[0], parent) or []
    else:
        prefix = []
    if outside != prefix + inside:
        return f'a condition in `{expr_str(result, parent)}` would bind another variable outside the block'
    return None
```

The bound variables of an expression, in order, as the kernel reads them. When a block closes,
its result is read at the parent level, where the block's constants are unknown; a condition like
`x ∈ A` that was read as binding `x` inside might read as binding `A` outside, if `x` is a
constant of the block that the parent doesn't know and `A` a variable. `k_reading_changes` compares
the reading of the result outside with the prefix the block adds (the names of a `let`, the
condition of an `assume`) followed by the reading of the last line inside; a difference is a
rejection (`binder_reading_changes` is the search's version). The prefix of a `let` is read from its
condition with the block's name stored in it (`bound_condition`), as the closed block gives it --
not from the condition alone: in `let w with $a <= w` inside `assume P $a`, the condition alone has
two variables, `$a` and `w` (before 2026-10-23 a rejection), but the block binds `w`; that it was new
in the block is checked by `forall-intro` (todo 52).

## 6. Closing a block: `kernel_verify_block`

When a block closes, `eval_done` makes a certificate whose `rule` is the block's last line, whose
`goal` is the formula the block gives, and whose `block` is the block's level (with its parent).
The kernel gets both levels read-only.

<!-- cite: kernel_verify_block :: def kernel_verify_block ... return k_reading_changes(block, parent, e, last.expr) -->
```python
def kernel_verify_block(cert: Certificate) -> Optional[str]:
    # closing a block: `cert.rule` is its last line, `cert.goal` the formula it gives
    assert cert.block is not None and cert.block.parent is not None and cert.rule is not None
    block, parent = k_env(cert.block), k_env(cert.block.parent)     # read-only, for this check
    last = cert.rule
    if not block.theory or block.theory[-1] is not last:
        return 'the last line is not the last line of the block'
    def new_in_block(c: str) -> bool:
        # a constant made by the block (`let`/`pick`), unknown outside of it -- or a variable, but
        # not one fixed by an enclosing assumption
        if parent.is_fixed_var(c):
            return False
        return parent.is_var(c) or (c in block.const and not parent.is_const(c) and not parent.is_used(c))
    witness = block.mode_args[0].value if block.mode_str == 'pick' and block.mode_args and isinstance(block.mode_args[0], Token) else None
    def no_escape(e: Expr) -> Optional[str]:
        # an individual constant of the block must not occur in what the block gives -- and the
        # witness of a `pick` never, even if it is also a "vocabulary" symbol (`prop`, `arity`)
        leaked = {c for c in k_constants(e, parent) if c in block.const and not parent.is_var(c)
                  and (not block.is_vocabulary_symbol(c) or c == witness)}
        if leaked:
            return f'the constants {sorted(leaked)} of the block occur in `{expr_str(e, parent)}`'
        return k_reading_changes(block, parent, e, last.expr)
```

`new_in_block` says whether a name was made by the block: a constant of the block that the parent
doesn't know (`let`/`pick`), or a variable -- but not one fixed by an enclosing assumption
(`is_fixed_var`: the `x` of an outer `assume R(x)` is "this x", and generalizing over it would be
wrong). `no_escape` checks that no constant of the block occurs in the result (a `let x` block
can't give a fact about `x`), with the witness of a `pick` never, even if it is also a vocabulary
symbol; and that the result reads the same outside.

<!-- cite: kernel_verify_block :: def sorts_kept ... return None -->
```python
def sorts_kept(names: list[str]) -> Optional[str]:
    # a constant of the block of a sort is a variable of that sort in the result (todo 34): `let
    # x` with `x + 1 > x` proves nothing about a set
    for v in names:
        inside = block.pos_sort(v, 0)
        if inside is None:
            continue
        outside = parent.generalized_sorts(v) or frozenset({'any'})     # (no sort: over all objects)
        if any(not k_sort_fits(o, inside, parent) for o in outside):
            return f'`{v}` has the sort `{inside}` in the block, but the result is about {"everything" if outside == {"any"} else "/".join(sorted(outside))}'
    return None
```

`sorts_kept` (todo 34): a constant of the block with a sort -- a `let x` that a line made a number
(`x + 1 > x`), the fixed `$x` of an `assume` -- is a variable of that sort in the result, or of a
smaller one: the variable the result is stored with gets its sort from the block
(`block_result_sorts`, which the search hands over as `generalized_sorts`), and if that were
missing, the result would be about everything. Checked for `impl-intro` and `not-intro` (the fixed
variables), `forall-intro` (the names and the fixed variables of a condition), and for
`exists-elim` the other way round: the witness has at most the sort of the existential's variable
(a witness of `∃ x` over everything is no number).

### 6.1 `assume` and `case`: `impl-intro` and `not-intro`

<!-- cite: kernel_verify_block :: match cert.kind: ... return sorts_kept(sorted(block.fixed_vars)) or no_escape(cert.goal) -->
```python
match cert.kind:
    case 'impl-intro' | 'not-intro':
        if block.mode_str not in ('assume', 'case') or len(block.mode_args) != 1:
            return 'not an `assume` or `case` block'
        assumption = block.mode_args[0]
        if cert.kind == 'impl-intro':
            expected: Expr = [Token('SYMBOL', IMPL_SYMBOL), assumption, last.expr]
        else:
            if not is_falsum(last.expr, parent):
                return 'the last line is not `false`'
            negation = negation_of(assumption, parent)
            if negation is None:
                return 'no symbol has the role of the negation'
            expected = negation
        if not k_equal(cert.goal, expected, parent):
            return f'`{expr_str(cert.goal, parent)}` is not `{expr_str(expected, parent)}`'
        return sorts_kept(sorted(block.fixed_vars)) or no_escape(cert.goal)
```

The block was opened by `assume A` or `case A` with one assumption. For `impl-intro` the result
must be `A ⇒ last`; for `not-intro` the last line must be `false` and the result the negation of
`A` (`negation_of`: the symbol with the role of the negation, §9).

### 6.2 `let`: `forall-intro`

<!-- cite: kernel_verify_block :: case 'forall-intro': ... return sorts_kept(list(block.let_names) + sorted(block.fixed_vars)) or no_escape(cert.goal) -->
```python
case 'forall-intro':
    if block.mode_str != 'let' or not block.mode_args:
        return 'not a `let` block'
    expected = last.expr
    if len(block.mode_args) != len(block.let_names):
        return 'a `let` block without its names'
    for condition, v in reversed(list(zip(block.mode_args, block.let_names))):
        if is_bool_var_token(condition, parent):
            continue
        if not new_in_block(v):
            return f'`{v}` was not new in the `let` block'
        if isinstance(condition, list):
            condition = bound_condition(v, condition)
        universal = parent.role_symbol('universal')
        if universal is None:
            return 'no symbol has the role of the universal quantifier'
        expected = [Token('SYMBOL', universal), condition, expected]
    if not k_equal(cert.goal, expected, parent):
        return f'`{expr_str(cert.goal, parent)}` is not `{expr_str(expected, parent)}`'
    return sorts_kept(list(block.let_names) + sorted(block.fixed_vars)) or no_escape(cert.goal)
```

For each name of the `let`, from the last to the first, the expected result gets one `∀` with
that name's condition (a bare `let x` has the variable as the condition; a `let x ∈ A` the
condition stored with its variable). A statement variable as a "name" (`let %A`, refused by `eval_let` since 2026-10-20) adds no quantifier. Each name must
have been new in the block.

### 6.3 `pick`: `exists-elim`

<!-- cite: kernel_verify_block :: case 'exists-elim': ... return f'unknown block rule -->
```python
    case 'exists-elim':
        if block.mode_str != 'pick' or len(block.mode_args) != 1 or block.pick_source is None or block.pick_fact is None:
            return 'not a `pick` block'
        witness = block.mode_args[0]
        if not (isinstance(witness, Token) and isinstance(witness.value, str) and new_in_block(witness.value)):
            return f'the witness `{expr_str(witness, parent)}` was not new in the `pick` block'
        if not k_known(block.pick_source, parent):
            return 'the existential fact is not in the theory'
        match block.pick_source.simplified_expr:
            case [Token(label='SYMBOL', value=q), Token(label='SYMBOL', value=x), body] if parent.has_role(q, 'existential') and isinstance(x, str):
                instance = normalize_expr(k_replace(body, x, witness, parent), parent)
            case [Token(label='SYMBOL', value=q), cond, body] if parent.has_role(q, 'existential') and isinstance(cond, list):
                # with a condition: the condition and the body ("exists-cond-def")
                x = k_bound(cond, parent)
                condition = cond[2] if cond[:1] and isinstance(cond[0], Token) and cond[0].value == BOUND_SYMBOL else cond   # (stored with its variable)
                instance = normalize_expr([Token('SYMBOL', AND_SYMBOL), k_replace(condition, x, witness, parent), k_replace(body, x, witness, parent)], parent)
            case _:
                return 'the fact picked from is not an existential'
        # the witness has at most the sort of the bound variable (todo 34): a witness of `∃ x`
        # over everything is not a number
        inside = block.pos_sort(witness.value, 0)
        if inside is not None:
            outside = parent.variable_sorts(x) or {'any'}     # (no sort: over all objects)
            if any(not k_sort_fits(o, inside, parent) for o in outside):
                return f'the witness `{witness.value}` has the sort `{inside}`, but the bound variable of the existential {"/".join(sorted(outside)) or "none"}'
        if not k_equal(instance, normalize_expr(block.pick_fact.expr, parent), parent):
            return f'the fact `{expr_str(block.pick_fact.expr, parent)}` about the witness is not `{expr_str(instance, parent)}`'
        if not k_equal(cert.goal, last.expr, parent):
            return 'the block does not give its last line'
        return no_escape(cert.goal)
return f'unknown block rule `{cert.kind}`'
```

`pick c with F` opened the block: the witness `c` must have been new, the existential fact it
was picked from must be in the theory, and the fact about the witness that the block started with
(`pick_fact`) must be the body of the existential with the witness for its variable -- with a
conditioned existential, the condition and the body conjoined. Then the block gives its last
line, in which the witness must not occur (`no_escape`).

## 7. Where the certificates come from

Three places in the search build certificates. `impl_elim` makes the `'rule'` ones, after it has
unified the goal with a formula (the `'fact'` form) or with the conclusion of a rule whose premise
it matched against the theory (`match_all_theory`, which also returns the fresh names of the `∀`s
it stripped, `strips`):

<!-- cite: impl_elim :: if premise is None:     # the goal is an instance of the formula ... return cert, s_final -->
```python
if premise is None:     # the goal is an instance of the formula
    cert = record_certificate(Certificate('rule', expr, expr_free_vars, proven_formula, 'fact', formula_expr, values=resolved_values(s_final)), kb)
else:
    assert matched_formulas is not None     # (the loop above only ends with a premise through `success`)
    cert = record_certificate(Certificate('rule', expr, expr_free_vars, proven_formula, 'impl', formula_expr,
                                   premise_fresh_vars, conclusion_fresh_vars, resolved_values(s_final),
                                   list(matched_formulas), strips), kb)

return cert, s_final    # bingo!  found an implication (and a substitution)
```

`resolved_values` resolves the final substitution of the unifier into plain values (the
certificate gives the values, not a chain of bindings). `eval_done` closes a block:

<!-- cite: close_block_with :: # the kernel checks the step, with the block's level ... filename, lines, own_lines=True) -->
```python
# the kernel checks the step, with the block's level (see `kernel_verify_block`)
block = kb
rule_name = {'assume': 'impl-intro', 'case': 'impl-intro', 'let': 'forall-intro', 'pick': 'exists-elim'}[mode_str]
# the result is numbered by the lines of the block (the next line has a number of its own)
lines = block_lines(block, kb.theory[-1])
reason = step_reason([record_certificate(Certificate(rule_name, expr, frozenset(), kb.theory[-1], block=block), block)],
                     filename, lines, own_lines=True)
```

(and, for an `assume` block that ends in `false`, a second certificate for the negation,
`not-intro`). The simple kinds come from `derive_expr_as_given`: a `todo` line (its certificate names the
`todo` as its rule), `true`, a computed comparison with `calc on`, a fact that computes to the
goal; `nary_case_elim` makes the `'case-elim'` one.

<!-- cite: derive_expr_as_given :: return [record_certificate(Certificate('todo' ... return [record_certificate(Certificate('calc-fact' -->
```python
            return [record_certificate(Certificate('todo', expr, frozenset(), kb.theory[-1]), kb)], s     # (`rule`: the `todo`, for `foundation`)

# rename variables
written = expr
expr, stripped = remove_outer_forall_quantifiers(expr, kb)
expr = rename_all_vars(expr, kb)    # rename variables

# "top-intro"
if isinstance(expr, Token) and expr.label=='SYMBOL' and expr.value==TRUE_SYMBOL:
    return [record_certificate(Certificate('top', expr, frozenset()), kb)], s

# "calc": with `calc on`, a comparison of two literal numbers is checked by computing it,
# and a fact that computes to `expr` (e.g. `x = (-5) * 5` for `x = -25`) gives `expr`
if kb.calc:
    if numeric_comparison_holds(expr, kb) or numeric_comparison_holds(calculate_normalized(expr, kb), kb):
        return [record_certificate(Certificate('calc', expr, frozenset()), kb)], s     # (`1 + 1 = 2`: computed)
    calc_expr = calculate_normalized(expr, kb)
    for f in kb.all_theory():
        if equal_expr(calculate_normalized(f.expr, kb), calc_expr, kb):
            return [record_certificate(Certificate('calc-fact', expr, frozenset(), f), kb)], s
```

## 8. Certificates on disk: replaying a `.kurtc`

A `.kurtc` file stores, for each line, the certificates of its steps as JSON (`certificate_to_json`,
`write_kurtc`). When the file is checked again, a stored certificate is a *hint*: before searching
for a line, `replay_certificate` tries the stored certificates of that line. A hint is rebuilt
against the goal and the theory as they are now -- the rule and the facts are looked up again
(`resolve_formula`), the fresh names are mapped to fresh names of this run -- and then handed to
the same `kernel_verify`. A hint the kernel rejects is simply not used; the search runs as if there
were none. So a `.kurtc` can make a check fast, never wrong (`doc/kurt-kernel.md` §6).

A line may have several certificates: the search derives *steps* of its own for some lines -- the
instance of a rule that a rewriting step needs (`17a` by `conditional_rewrite`), the line with one
place rewritten (`multi_rewrite`) -- and adds each to the theory with its certificate before the
line's certificate cites it as a fact. Rebuilt on its own, the line's certificate would fail: `17a`
is not in the theory yet. So `rebuild_certificate` derives such a fact first, from the stored
certificate whose goal is that formula (`replay_step`): checked by the kernel like any other, and
added to the theory with its number, as the search added it. The kernel knows a fact by identity
(`k_known`), so the step must be in the theory before the line's certificate is checked -- and a
step that doesn't check (or has no certificate) takes the line's certificate down with it, and the
search runs as without a `.kurtc` (2026-10-16; before, every step of a chain was searched again,
with the certificates present).

<!-- cite: def rebuild_certificate -->
```python
def rebuild_certificate(h: dict, names: dict[str, str], goal: Expr, fixed: frozenset[str], kb: KnowledgeBase,
                        steps: Optional[ReplaySteps] = None) -> Optional[Certificate]:
    # a stored certificate (see `certificate_to_json`) for the goal and facts as they are now --
    # a fact that is a step of the line (`17a`) is derived first from its own certificate (`steps`)
    rule = resolve_formula(h['rule'], names, kb)
    if rule is None:
        return None
    facts: list[Formula] = []
    for j in h['facts']:
        f = resolve_formula(j, names, kb)
        if f is None and steps is not None and replay_step(j, kb, steps):
            f = resolve_formula(j, names, kb)
        if f is None:
            return None
        facts.append(f)
    return Certificate('rule', goal, fixed, rule, h['form'], rule.simplified_expr,
                       tuple(fresh_name(c, names) for c in h['premise_fresh']), tuple(fresh_name(c, names) for c in h['conclusion_fresh']),
                       {fresh_name(c, names): canonical_to_fresh(expr_from_json(v), names) for c, v in h['values']},
                       facts, [tuple(fresh_name(c, names) for c in fresh) for fresh in h['fact_fresh']])
```

<!-- cite: def replay_step -->
```python
def replay_step(j: dict, kb: KnowledgeBase, steps: ReplaySteps) -> bool:
    # a fact of a stored certificate that is a step of the line itself -- `17a`, the instance of a
    # rule that a rewriting step needs (`conditional_rewrite`), or the line with one place
    # rewritten (`multi_rewrite`) -- which the search derives first and adds to the theory. It is
    # derived here as the search would: from its own stored certificate (the one for its formula),
    # checked by the kernel, and added with its number; its facts may be steps too. So a chain line
    # replays as a whole, which the search then doesn't run (field.kurt with its certificates: 2.7 s
    # before, 0.5 s now; 4.6 s without them; 2026-10-16). Without the step's certificate, or if the kernel
    # rejects it, the line's certificate can't be rebuilt, and the search runs as without it.
    key = run_state.current_line[0]
    assert key is not None
    if j['label'] or j['direction'] is not None or portable_file(j['file']) != portable_file(key[0]) \
            or not re.fullmatch(rf'{key[1]}[a-z]+', str(j['line'])):
        return False
    if any(g.line == j['line'] for g in kb.all_theory()):
        return False                        # (its number is taken, see `next_sub_line`)
    wanted = canonical_json(j['expr'])
    for h in steps.hints:
        if any(h is u for u in steps.used) or canonical_json(h['goal']) != wanted:
            continue
        steps.used.append(h)                # (also while it is rebuilt: a step is no fact of its own)
        before, added_before = len(kb.theory), len(steps.added)
        names: dict[str, str] = {}
        goal = canonical_to_fresh(expr_from_json(h['goal']), names)
        cert = rebuild_certificate(h, names, goal, frozenset(free_bound_vars(goal, kb)[0]), kb, steps)
        if cert is None or kernel_verify(cert, kb) is not None:
            del kb.theory[before:], steps.added[added_before:]      # (steps it needed, and it isn't one)
            continue
        line_str = str(j['line'])
        reason = step_reason([cert], key[0], line_str)
        step = Formula(kb, goal, expr_str(goal, kb), line_str, key[0], '', reason, keyword='')
        kb.theory_append(step)
        steps.added.append((step, cert))
        return True
    return False
```

<!-- cite: def replay_certificate -->
```python
def replay_certificate(goal: Expr, fixed: frozenset[str], kb: KnowledgeBase) -> tuple[Optional[Certificate], bool]:
    # a stored certificate of the current line for `goal`, accepted by the kernel (with the
    # steps of the line it needs, `replay_step`) -- and whether the line has stored certificates
    # at all
    key = run_state.current_line[0]
    if key is None or key[0] not in run_state.replay_hints:
        return None, False
    hints = run_state.replay_hints[key[0]].get(key[1])
    if not hints:
        return None, False
    for h in list(hints):
        before = len(kb.theory)
        steps = ReplaySteps(hints)
        try:
            names: dict[str, str] = {}
            if not align(expr_from_json(h['goal']), goal, names):
                continue
            cert = rebuild_certificate(h, names, goal, fixed, kb, steps)
            if cert is None or kernel_verify(cert, kb) is not None:
                del kb.theory[before:]      # (the steps replayed for it)
                continue
        except Exception:       # a damaged `.kurtc`: only a hint that doesn't work
            del kb.theory[before:]
            continue
        hints[:] = [g for g in hints if g is not h and not any(g is u for u in steps.used)]
        for step, step_cert in steps.added:
            run_state.certificates_by_line.setdefault(key, []).append((step_cert, None))
            log(kb, step.formula_str(kb), step.reason, kb.level)      # (as the search shows a step it derived)
        run_state.replayed += 1 + len(steps.added)
        run_state.certificates_by_line.setdefault(key, []).append((cert, None))
        return cert, True
    return None, True
```

## 9. What the kernel trusts

The kernel is small by trusting a few things outside it, each of which is also exercised by every
proof file of the test suite:

- the parser, which turns the text of the `.kurt` file into the `Expr` trees;
- `normalize_expr` (`flat`, `sym`, and the calculator when `calc` is on): the one normal form
  that every line and every instance goes through, so that "equal" means "equal after
  normalizing";
- `calculate_normalized` and `numeric_comparison_holds`, the calculator, for `calc` steps;
- `negation_of` and `is_falsum` (the symbols with the roles of the negation and of `false`),
  `bound_condition` (storing a condition with its variable), `new_var_name` and
  `new_bool_var_name` (fresh names), `is_ellipsis`, `get_token_set`, `expr_str` (printing, for
  messages only);
- the `KnowledgeBase` lookups of `KbReader`, as they are at the moment of the check.

What the kernel does *not* trust is everything the search computed: the unifier's substitution,
which `∀`s it stripped, which variable a binder binds, whether a value may be captured, whether a
constant escaped a block. Each of these is read again by a `k_*` function.

How this is tested: every step of every proof, theory, lesson and exercise in the suite goes
through `record_certificate`, and a rejection anywhere fails the suite. `tests/test_kernel.py`
takes real certificates and breaks them -- no facts, another goal, a rule not in the theory, a
value for a goal variable, a value that depends on a fresh variable, a capture; for blocks another
result, a missing `∀`, not the last line, a witness that escapes -- and the kernel must reject each
one. `tests/test_kernel_boundary.py` checks that the kernel calls no search code and reads binders
and equality on its own; `tests/test_kernel_env.py` that the view is read-only;
`tests/test_kernel_differential.py` compares `k_equal` and `k_replace` with the search's
`equal_expr` and `capture_avoiding_replace` on generated terms with binders, a `sym` operator and
shadowing. And `tests/test_kernel_literate.py` keeps this document the code.
