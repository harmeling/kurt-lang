#!/usr/bin/env python3
from __future__ import annotations

## kurt.py
# kurt - a programming language for proof writing and checking
# (c) 2025 Stefan Harmeling
# licensed under the MIT License

## for profiling run:
# python -m cProfile -o kurt.prof kurt.py
# python -m cProfile -s time kurt.py proofs/linear-algebra/group.kurt

## merge the dev into main branch:
# git checkout main && git pull && git merge dev && git push

## processing a kurt-file does the following steps in a single pass
# level1: lexing
# level2: parsing
# level3: simple type checking
# level4: proving

## link to a good explanation of the natural deduction system
# https://leanprover-community.github.io/logic_and_proof/natural_deduction_for_first_order_logic.html


## all external libraries (let's keep the dependencies minimal)
import sys
if sys.version_info < (3, 10):
    print("Python 3.10 or newer is required, since we are using Python's `match`!  Sorry about that!", file=sys.stderr)
    exit(0)
import os           # os.path.[isfile, dirname, abspath, join, basename, split, expanduser, exists]
import argparse     # argparse.ArgumentParser
import re           # re.[compile, sub, VERBOSE, MULTILINE]
import atexit       # atexit.register
import inspect      # inspect.stack

import itertools    # itertools.[product, count, chain, permutations]
from dataclasses import dataclass
from typing import TypeAlias, Literal, Callable, TypeVar, Generic, Iterator, TextIO, Optional

try:
    # should work under Linux and MacOS, but not under Windows
    import readline     # readline.[parse_and_bind, read_history_file, write_history_file]
except ImportError:
    # sorry, Windows users, no readline support
    # print("Warning: readline not available. Line editing features will be limited.")
    readline = None

# config: general information
version        = 0.1
made_by        = 'made by Stefan Harmeling, 2025'

# config: the indentation for the different blocks
md_indent      =  7       # for markdown files ignore all lines not starting with `md_indent` many spaces
proof_indent   =  4       # how much to indent for a `proof` block
reason_indent  = 60       # how much the reason is indented
tab_indent     =  4       # tabs get converted to four spaces

# config: the basic symbols of the kurt language as constants
AND_SYMBOL   = 'and'         # conjunction (used for premises and conclusions)
IMPL_SYMBOL  = 'implies'     # implication 
SUB_SYMBOL   = 'sub'         # substitution
NOT_SYMBOL   = 'not'         # negation
TRUE_SYMBOL  = 'true'        # true
FALSE_SYMBOL = 'false'       # false
COMMA_SYMBOL = ','           # listing stuff
SPACE_SYMBOL = ' '           # function application

# not basic, but still necessary for our implementation of forall-intro and exists-intro
FORALL_SYMBOL = 'forall'     # universal quantification
EXISTS_SYMBOL = 'exists'     # existential quantification
EQUAL_SYMBOL  = '='          # equality
IFF_SYMBOL    = 'iff'        # equivalence

# config: the default theory and default path
default_theory: str    = 'theory.kurt'                                                   # default theory
this_file_path: str    = os.path.dirname(os.path.abspath(__file__))                      # path of THIS file
theory_path: list[str] = ['.', 'theories', os.path.join(this_file_path, 'theories')]     # default path for theories

debug_flag = False
debug_counter = 0
def debug(*s) -> None:
    if debug_flag:
        global debug_counter
        caller = inspect.stack()[1].function
        print(f'{debug_counter:03} DEBUG[{caller}]:', ' '.join(map(str, s)), file=sys.stdout)
        if debug_counter == 295:
            pass
        debug_counter += 1

## some pretty replacement of latex style symbols with unicode characters
REPLACEMENTS: dict[str, str] = {
    # propositional logic
    '\\not':     '¬',
    '\\neg':     '¬',
    '\\and':     '∧',
    '\\or':      '∨',
    '\\iff':     '⇔',
    '\\equiv':   '≡',
    '\\implies': '⇒',
    '\\invimplies': '⇐',
    '\\bottom':  '⊥',
    '\\top':     '⊤',

    # first order logic
    '\\forall':  '∀',
    '\\exists':  '∃',

    # modal logic
    '\\box':     '□',      # necessity
    '\\b':       '□',
    '\\diamond': '◇',      # possibility
    '\\d':       '◇',

    # set theory
    '\\infty':    '∞',     # infinity
    '\\in':       '∈',     # element of
    '\\notin':    '∉',     # not element of
    '\\subset':   '⊂',     # proper subset
    '\\subseteq': '⊆',     # subset or equal
    '\\supset':   '⊃',     # proper superset
    '\\supseteq': '⊇',     # superset or equal
    '\\cap':      '∩',     # intersection
    '\\cup':      '∪',     # union
    '\\emptyset': '∅',     # empty set
    '\\equiv':    '≡',     # equivalence
    '\\circ':     '∘',     # function composition

    # numbers
    '\\leq': '≤',          # less than or equal
    '\\geq': '≥',          # greater than or equal
    '\\neq': '≠',          # not equal

    # small Greek letters
    '\\alpha':   'α',
    '\\beta':    'β',
    '\\gamma':   'γ',
    '\\delta':   'δ',
    '\\epsilon': 'ε',
    '\\zeta':    'ζ',
    '\\eta':     'η',
    '\\theta':   'θ',
    '\\iota':    'ι',
    '\\kappa':   'κ',
    '\\lambda':  'λ',
    '\\mu':      'μ',
    '\\nu':      'ν',
    '\\xi':      'ξ',
    '\\omicron': 'ο',
    '\\pi':      'π',
    '\\rho':     'ρ',
    '\\sigma':   'σ',
    '\\tau':     'τ',
    '\\upsilon': 'υ',
    '\\phi':     'φ',
    '\\chi':     'χ',
    '\\psi':     'ψ',
    '\\omega':   'ω',

    # capital Greek letters
    '\\Alpha':   'Α',
    '\\Beta':    'Β',
    '\\Gamma':   'Γ',
    '\\Delta':   'Δ',
    '\\Epsilon': 'Ε',
    '\\Zeta':    'Ζ',
    '\\Eta':     'Η',
    '\\Theta':   'Θ',
    '\\Iota':    'Ι',
    '\\Kappa':   'Κ',
    '\\Lambda':  'Λ',
    '\\Mu':      'Μ',
    '\\Nu':      'Ν',
    '\\Xi':      'Ξ',
    '\\Omicron': 'Ο',
    '\\Pi':      'Π',
    '\\Rho':     'Ρ',
    '\\Sigma':   'Σ',
    '\\Tau':     'Τ',
    '\\Upsilon': 'Υ',
    '\\Phi':     'Φ',
    '\\Chi':     'Χ',
    '\\Psi':     'Ψ',
    '\\Omega':   'Ω'
}

# for the scanner
SPECIAL_SYMBOLS = ''.join(sorted(set(''.join(REPLACEMENTS.values()))))

# match any known command inside the string (even if joined to other text)
COMMAND_RE = re.compile('|'.join(re.escape(k) for k in sorted(REPLACEMENTS, key=len, reverse=True)))

def replace_latex_syntax(line: str) -> str:
    def command_replacer(match: re.Match) -> str:
        command = match.group(0)
        return REPLACEMENTS.get(command) or command
    return COMMAND_RE.sub(command_replacer, line)

class KurtException(Exception):
    def __init__(self, msg:str, column:Optional[int]=None, line:Optional[int]=None, filename:Optional[str]=None) -> None:
        self.msg:      str           = msg
        self.column:   Optional[int] = column
        self.line:     Optional[int] = line
        self.filename: Optional[str] = filename

## the syntax is stored in a hierarchical knowledge base called `KnowledgeBase`
format_options: list[Format] = ['sexpr', 'normal']         # sexpr: (+ 1 (* 3 4)), normal: (1 + (3 * 4))
keywords: dict[str, str] = {
    'help':        'print this help',
    'parse':       'parse a string and print its representation',
    'tokenize':    'tokenize a string and print its tokens',
    'format':      'choose print representation, i.e. one of "sexpr", "normal"',
    'level':       'print current level of the knowledge base',
    'mode':        'print current mode of the knowledge base, one of `root`, `proof`, `assume`, `fix`, `pick`',
    'context':     'print the current context, i.e., all open blocks and their modes',
    'trail':       'print the current context without details in one line',
    'load':        'load file(s), e.g. load standards.kurt or load foo.kurt',

    'syntax':      'print the current syntax',
    'prefix':      'add prefix operator with right binding power',
    'infix':       'add infix operator with left/right binding powers (lhb, rhb), note: lhb < rhb means right associative',
    'postfix':     'add postfix operator with left binding power',
    'brackets':    'declare brackets',
    'arity':       'set arity of a symbol (default is 0)',
    'bindop':      'declare a binding operator',
    'flat':        'declare infix operator to be flat',
    'sym':         'declare infix operator to be symmetric',
    'bool':        'declare symbols to have output type boolean',
    'chain':       'declare a chain of symbols, for automatic transitivity',
    'var':         'declare symbols as variable',
    'const':       'declare symbols as fresh constants, i.e., they have not been used or declared before',
    'alias':       'add some aliases for a symbol',

    'theory':      'print all formulas',
    'implications':'print all implications',

    # formulas
    'use':         'use a formula without proof as a axiom',
    'def':         'define new constant symbol using an equation or equivalence',

    'show':        'plan to prove a formula',
    'proof':       'start a proof block to prove the last planned formula',
    'qed':         'end a proof block, to finish the proof of the last planned formula',

    'todo':        'without a formula it is a joker for the next one, with a formula it is a joker for that one',

    # opening blocks
    'assume':      'open a block and assume a formula, the block must be finished with `thus`, made for `impl-intro`',
    'fix':         'fix a new constant, possibly as an assumption, the block must be finished with `thus`, made for `forall-intro`',
    'pick':        'picks a new constant `with` assumption, made for `exists-elim`',

    # closing blocks
    'thus':        'finish a block that was started with `assume`, `fix` or `pick`, and prove the given formula using the previous block',
    'break':       'break the current proof block without proving anything, should only be used in the shell'
    }
helper_keywords = ['with']     # for keyword `pick`, e.g., `pick y with F(y)`

keywords_with_parsing = ['use', 'show', 'def', 'assume', 'fix', 'thus', 'todo', 'parse']

# types
Label:  TypeAlias = Literal['SYMBOL', 'INT', 'FLOAT', 'STRING', 'END', 'TODO']
Value:  TypeAlias = str | int | float
Format: TypeAlias = Literal['sexpr', 'normal']

@dataclass
class Token:
    label: Label
    value: Value
    column: Optional[int] = None
    origin: Optional[Value] = None

    def __repr__(self) -> str:
        return f'{self.value}'

    def clone(self, new_value: Value) -> Token:
        return Token(
            label  = self.label,
            value  = new_value,
            column = self.column,
            origin = self.origin
        )
    
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Token):
            return NotImplemented
        return (self.label == other.label) and (self.value == other.value)

    def __hash__(self) -> int:
        # to use Token as keys in sets or dictionaries
        return hash((self.label, self.value))

class Formula:
    next_id: int = 0
    def __init__(self, kb: KnowledgeBase, expr:Expr, line:str, filename:str, label:str, reason:str, keyword:str):
        self.expr: Expr            = expr               # expression of the formula
        self.simplified_expr = expr
        self.simplified_expr: Expr = remove_outer_forall_quantifiers(self.simplified_expr, kb)
        self.simplified_expr: Expr = rename_all_vars(self.simplified_expr, kb)
        self.line: str             = line               # line of this formula, string since we also want '16a', etc
        self.filename: str         = filename           # file of this formula
        self.label: str            = label              # basically, a name of the formula, e.g., "impl-intro"
        self.reason: str           = reason             # the reason for this formula, e.g., "axiom", "assumption", "def", "by"
        self.keyword: str          = keyword            # one of `use`, `assume`, `show`, `todo`
        self.id: int               = Formula.next_id    # a unique id for every formula
        Formula.next_id += 1

    def is_proven(self) -> bool:
        # proven if `self.keyword in ['', 'todo']`
        # not proven is `self.keyword in ['use', 'show']`
        return self.keyword in ['', 'todo']

    def clone(self, new_expr: Expr, kb: KnowledgeBase) -> Formula:
        cloned_f = Formula(
            kb,
            expr     = new_expr,
            line     = self.line,
            filename = self.filename,
            label    = self.label,
            reason   = self.reason,
            keyword  = self.keyword
        )
        cloned_f.id = self.id
        return cloned_f

    def prefix_str(self) -> str:
        if self.keyword == '':
            return ''
        else:
            return f'{self.keyword} '
    
    def label_str(self) -> str:
        return f' "{self.label}"'
    
    def __str__(self) -> str:
        return f'{self.prefix_str()}{self.expr}{self.label_str()}'

    def __repr__(self) -> str:
        return str(self)

    # this function is necessary, since it requires the knowledgebase
    def formula_str(self, kb: KnowledgeBase) -> str:
        return f'{self.prefix_str()}{expr_str(self.expr, kb)}'

# expression
# not a class itself, instead just a type alias
Expr: TypeAlias = list["Expr"] | Token

def get_token_set(e: Expr) -> set[Token]:
    def get_token_list(e: Expr) -> list[Token]:
        if isinstance(e, list):
            tokens: list[Token] = []
            for item in e:
                tokens += get_token_list(item)
            return tokens
        else:
            return [e]
    return set(get_token_list(e))

def deepcopy_expr(expr: Expr) -> Expr:
    if isinstance(expr, Token):
        # Use shallow copy or clone to retain metadata if needed
        return Token(expr.label, expr.value, expr.column, expr.origin)
    elif isinstance(expr, list):
        # Recursively copy the sub-expressions
        return [deepcopy_expr(e) for e in expr]
    else:
        assert False, f'Never reach this case!'

# a useful tool for parsing:
T = TypeVar('T')
class PeekableGenerator(Generic[T]):                 # a peekable generator
    def __init__(self, gen: Iterator[T]) -> None:
        self.gen: Iterator[T]  = gen                  # the generator
        self.eog: bool         = False                # end-of-generator, are we done yet?
        self.peek: Optional[T] = None                 # initial peek is None
        self._advance()                              # possibly modifies self.eog
    def __iter__(self) -> PeekableGenerator[T]:
        return self
    def __next__(self) -> T:
        if self.eog:
            raise StopIteration
        assert self.peek is not None
        current: T = self.peek
        self._advance()
        return current
    def _advance(self) -> None:
        try:
            self.peek = next(self.gen)               # update the peek
        except StopIteration:                        # delay the exception until the next 'next'-call
            self.peek = None                         # nothing to peek anymore
            self.eog = True                          # next call __next__ triggers the exception
    def prepend(self, item: T) -> None:
        if self.peek is not None:
            self.gen = itertools.chain([self.peek], self.gen)   # shift the peek back to the front
        self.peek = item                             # set the peek to the new item
        self.eog  = False                            # we are not at the end of the generator

# the state for the unification combines a substitution and a set of blocked variables
@dataclass(frozen=True)
class State:
    subst: dict[str, Expr]
    blocked_as_domain: frozenset[str]
    blocked_as_range: frozenset[str]

    @staticmethod
    def empty() -> State:
        """Initial state with no substitutions and no blocked vars."""
        return State({}, frozenset(), frozenset())

    # lookup
    def lookup(self, v: str) -> Optional[Expr]:
        """Return the expression v is bound to, or None if unbound."""
        return self.subst.get(v)

    def is_blocked_as_domain(self, v: str) -> bool:
        """Check if a variable is blocked as a domain variable."""
        return v in self.blocked_as_domain

    def is_blocked_as_range(self, v: str) -> bool:
        """Check if a variable is blocked as a range variable."""
        return v in self.blocked_as_range

    # updates (return new States)
    def bind(self, v: str, e: Expr) -> State:
        new_subst = dict(self.subst)   # shallow copy
        new_subst[v] = deepcopy_expr(e)
        return State(new_subst, self.blocked_as_domain, self.blocked_as_range)

    def block_as_domain(self, v: str) -> State:
        # this is for free variables of the goal, e.g.,
        #   use A, B ⇒ C
        #   D
        # to prove D we first unify D with C, but must block the free variables of D as domain
        return State(dict(self.subst), self.blocked_as_domain | {v}, self.blocked_as_range)

    def block_always(self, v: str) -> State:
        # this is for blocking bound variables
        return State(dict(self.subst), self.blocked_as_domain | {v}, self.blocked_as_range | {v})

    def unblock(self, v: str) -> State:
        return State(dict(self.subst), self.blocked_as_domain - {v}, self.blocked_as_range - {v})

    # walk and occurs
    def walk(self, e: Expr) -> Expr:
        # head-normalize a SYMBOL token through `self.subst`, 
        # stopping at binders (blocked),
        # with a small cycle guard. 
        # lists are not traversed (by design).
        visited: set[str] = set()
        while isinstance(e, Token) and e.label == 'SYMBOL':
            u = e.value
            assert isinstance(u, str)
            if self.is_blocked_as_domain(u):
                break
            if u in visited:             # cycle guard
                break
            visited.add(u)
            t: Optional[Expr] = self.lookup(u)
            if t is None:
                break
            # avoid trivial self-map loops: $x -> $x
            if isinstance(t, Token) and t.label == 'SYMBOL' and t.value == u:
                break
            e = t
        return e

    # occurs check: does variable v appear inside expr (after walking)?
    def occurs(self, v: str, e: Expr) -> bool:
        e = self.walk(e)
        match e:
            case Token(label='SYMBOL', value=u):
                #if isinstance(u, str) and (kb.is_var(u) or kb.is_bool_var(u)):
                return v == u
            case [*children]:
                return any(self.occurs(v, child) for child in children)
            case _:
                return False
            
    def contains_blocked_as_range(self, e: Expr) -> bool:
        e = self.walk(e)
        match e:
            case Token(label='SYMBOL', value=u) if isinstance(u, str):
                # treat blocked names as rigid atoms
                return self.is_blocked_as_range(u)
            case [*children]:
                return any(self.contains_blocked_as_range(c) for c in children)
            case _:
                return False

# hierarchical knowledge base
# the level is increased inside blocks and files
# dropping a level drops also all local definitions
Nud: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Token], Expr]
Led: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Expr, Token], Expr]
Mode: TypeAlias = tuple[str, Expr]  # where the str is one of ['root', 'proof', 'assume', 'fix', 'pick']

class KnowledgeBase:
    def __init__(self, parent:Optional[KnowledgeBase]=None, mode: Mode=('root', [])) -> None:
        # general
        self.parent: Optional[KnowledgeBase] = parent
        self._todos: list[str]     = []                   # list of todos (only relevant on level 0)
        self.level: int            = 0 if parent is None else parent.level + 1
        self.mode_str: str         = mode[0]              # one of ['root', 'proof', 'assume', 'fix', 'pick']
        self.mode_expr: Expr       = mode[1]              # the expression that opened the current block (empty for 'root' and 'proof')
        self.libs: list[str]       = []                   # the filenames of loaded libraries

        # syntax
        self.infix:    dict[str, tuple[int,int]] = {}     # left and right binding powers of infix operators
        self.postfix:  dict[str, int]            = {}     # left binding power of postfix operator
        self.prefix:   dict[str, int]            = {}     # right binding power of prefix operator
        self.brackets: dict[str, str]            = {}     # keys are right brackets, values are left brackets
        self.arity:    dict[str, int]            = {}     # for non-zero arities
        self.chain:    list[list[str]]           = []     # for chaining operators, i.e., 18 = 1+17 <= 20 < 21
        self.bindop:   set[str]                  = set()  # set for variable binding operators
        self.flat:     set[str]                  = set()  # set for declaring a flat operator, i.e., ($a + $b) + $c = $a + $b + $c
        self.sym:      set[str]                  = set()  # set for declaring a symmetric operator, i.e., $a + $b = $b + $a
        self.alias:    dict[str, str]            = {}     # dict of alias pointing to the original
        self.used:     set[str]                  = set()  # set of all symbols that are used in formulas (i.e., not only declared)

        # parsing related
        self.lbp:      dict[str, int]            = {}     # left binding power
        self.rbp:      dict[str, int]            = {}     # right binding power
        self.nud:      dict[str, Nud]            = {}     # null denotation, entries are functions for parsing expressions
        self.led:      dict[str, Led]            = {}     # left denotation, entries are functions for parsing infix expressions

        # variables vs constants
        self.var:      set[str]                  = set()  # set of variables with unused values
        self.const:    set[str]                  = set()  # set of constants with unused values

        # types
        self.bool:     dict[str, list[int]]      = {}     # dict of symbols declared to have boolean output

        # theory
        self.theory: list[Formula] = []                   # list of formulas (axioms added by 'use' or 'todo', 
                                                          #                   assumptions added by 'assume',
                                                          #                   and derived formulas)
        self.show:   list[Formula] = []                   # lists of promised formulas to show

        # misc
        self.format: Format = format_options[1] if parent is None else parent.format  # how formulas look in the shell
        self.verbose: bool  = False if parent is None else parent.verbose           # extra information or not

    def nice_mode_str(self) -> str:
        if isinstance(self.mode_expr, list):
            args_str = ", ".join([f'{expr_str(v, self)}' for v in self.mode_expr])
        else:
            args_str = expr_str(self.mode_expr, self)
        return f'{">"*self.level}! {self.mode_str} {args_str}'

    def todo_add(self, todo) -> None:
        if self.parent is None:
            self._todos.append(todo)
        else:
            self.parent.todo_add(todo)

    def todos(self) -> list[str]:
        if self.parent is None:
            return self._todos
        else:
            assert len(self._todos) == 0, f'BUG: `todos` must be stored in the top level'
            return self.todos()

    def _entry_str(self, keyword:str, key:str, value:str|int|tuple[int,int]|list[int]|list[str]|None = None) -> str:
        if   keyword == 'prefix':   return f'prefix {key} {value}'
        elif keyword == 'infix':    
            assert isinstance(value, tuple) and len(value) == 2, f'BUG!  Unexpected value for `infix`, got {value}'
            if key == ' ':
                return f'infix " " {value[0]} {value[1]}'
            else:
                return f'infix {key} {value[0]} {value[1]}'
        elif keyword == 'postfix':  return f'postfix {key} {value}'
        elif keyword == 'brackets': return f'brackets {value} {key}'
        elif keyword == 'chain':    return f'chain {" ".join(key)}'
        elif keyword == 'arity':    return f'arity {key} {value}'
        elif keyword == 'flat':     return f'flat {key}'
        elif keyword == 'sym':      return f'sym {key}'
        elif keyword == 'bindop':   return f'bindop {key}'
        elif keyword == 'bool':     
            assert isinstance(value, list), f'BUG!  Unexpected value for `bool`, got {value}'
            return f'bool {key} {" ".join(map(str, value))}'
        elif keyword == 'var':      return f'var {key}'
        elif keyword == 'const':
            if key == ' ':
                return f'const " "'
            else:
                return f'const {key}'
        elif keyword == 'alias':    return f'alias {key} {value}'
        else: 
            assert False, f'BUG: unknown keyword, got {keyword}'

    def dict_or_set_str(self, keyword: str, key: Optional[str]=None) -> str:
        some_dict_or_set: dict[str, str|int|tuple[int,int]|list[int]|list[str]]|set[str] = getattr(self, keyword)
        def select(k: str) -> bool:
            if key is None:
                return True
            else:
                return key == k
        if isinstance(some_dict_or_set, dict):
            lines = [self._entry_str(keyword, k, some_dict_or_set[k]) for k in some_dict_or_set if select(k)]
            # next check whether the values of the dicts are strings, if yes, check for key there as well
            if key is not None:
                d = some_dict_or_set
                if isinstance(next(iter(d.values()), None), str):   # check whether the values are strings
                    for key_for_value in (k for k, v in d.items() if v == key):
                        lines += [self._entry_str(keyword, key_for_value, some_dict_or_set[key_for_value])] 
        else:
            lines = [self._entry_str(keyword, key) for key in some_dict_or_set if select(key) ]

        # put the level at indent 42
        lines = [f'{line:<42} ; level {self.level}' for line in lines]
        lines.sort()
        return '\n'.join(lines)

    def dict_or_set_str_all_levels(self, keyword: str) -> str:
        s: str = ''
        if self.parent is not None:
            s += self.parent.dict_or_set_str_all_levels(keyword) + '\n'
        s += self.dict_or_set_str(keyword)
        return s

    # SYNTAX RELATED
    def info(self, t: Token) -> str:
        label, value = t.label, t.value
        if label == 'SYMBOL':
            assert isinstance(value, str)
            return self.syntax_str_all_levels(value)
        elif label == 'INT':
            return f'; `{str(value)}` is an integer'
        elif label == 'FLOAT':
            return f'; `{str(value)}` is a float'
        elif label == 'STRING':
            return f'; "{value}" is a string'
        else:
            return ''

    def syntax_str_all_levels(self, key: Optional[str]=None) -> str:
        s = ''
        if self.parent is not None:
            s += self.parent.syntax_str_all_levels(key) + '\n'
        all_syntax = [self.dict_or_set_str('prefix', key),
                        self.dict_or_set_str('infix', key),
                        self.dict_or_set_str('postfix', key),
                        self.dict_or_set_str('arity', key),
                        self.dict_or_set_str('chain', key),
                        self.dict_or_set_str('bindop', key),
                        self.dict_or_set_str('brackets', key),
                        self.dict_or_set_str('flat', key),
                        self.dict_or_set_str('sym', key),
                        self.dict_or_set_str('alias', key),
                        self.dict_or_set_str('var', key),
                        self.dict_or_set_str('const', key),
                        self.dict_or_set_str('bool', key)]
        s += '\n'.join([syntax for syntax in all_syntax if syntax != ''])
        s += '\n'    # we should end with a newline
        return s

    def is_infix(self, s: str) -> bool:
        return s in self.infix   or (self.parent is not None and self.parent.is_infix(s))

    def is_prefix(self, s: str) -> bool:
        return s in self.prefix  or (self.parent is not None and self.parent.is_prefix(s))

    def is_postfix(self, s: str) -> bool:
        return s in self.postfix or (self.parent is not None and self.parent.is_postfix(s))

    def is_bindop(self, s: str) -> bool:
        return s in self.bindop  or (self.parent is not None and self.parent.is_bindop(s))

    def is_flat(self, s: str) -> bool:
        return s in self.flat    or (self.parent is not None and self.parent.is_flat(s))

    def is_sym(self, s: str) -> bool:
        return s in self.sym     or (self.parent is not None and self.parent.is_sym(s))

    def is_var(self, s: str) -> bool:
        if s in self.const:
            assert s not in self.var
            return False
        else:
            return s[0] == '$' or s in self.var or (self.parent is not None and self.parent.is_var(s))

    def is_local_var(self, s: str) -> bool:                # check only in the current level, used for `add_const`
        return s in self.var

    def is_bool_var(self, s: str) -> bool:
        # e.g. variable for formulas (in `sub x a A` the symbol `A` is boolean)
        if s in self.const:
            assert s not in self.var
        if s[0] == '%':
            return True
        if self.is_var(s):
            return 0 in self.bool_sig(s)
        return False

    def is_const(self, s: str) -> bool:
        if s in self.var:
            assert s not in self.const
            return False
        else:
            return s in self.const   or (self.parent is not None and self.parent.is_const(s))

    def is_chainable(self, s: str) -> bool:
        for c in self.all_chains():
            if s in c:
                return True
        return False

    def starts_a_chain(self, e: Expr) -> bool:
        if isinstance(e, list) and len(e) == 3:   # must be infix operator
            e0 = e[0]
            if isinstance(e0, Token) and isinstance(e0.value, str):
                if self.is_chainable(e0.value):
                    return True
        return False

    def get_chain_op(self, chain_so_far: list[str]) -> Optional[str]:
        # find the chain that matches `chain_so_far` and return the operator that is at the largest index matched so far
        for c in self.all_chains():
            try:
                indices: list[int] = []
                for op in chain_so_far:
                    indices.append(c.index(op))
                return c[max(indices)]
            except ValueError:
                continue
        return None

    # all chains define a transitive relation without cycles, i.e., a directed acyclic graph (DAG)
    def check_with_other_chains(self, c: list[str]) -> None:
        # a chain `c` must not be in conflict with the ordering of the other chains
        for other_c in self.all_chains():
            current = -1  # `current` must go through an strictly increasing sequence for all other chains
            for op in c:
                if op in other_c:
                    idx = other_c.index(op)     # might raise ValueError
                    if idx <= current:
                        raise KurtException(f'EvalError: chain `{c}` is in conflict with `{other_c}`, creates a cycle')
                    current = idx

    def is_used(self, s: str) -> bool:
        return s in self.used    or (self.parent is not None and self.parent.is_used(s))

    def is_alias(self, s: str) -> bool:
        return s in self.alias   or (self.parent is not None and self.parent.is_alias(s))

    def bool_sig(self, s: str) -> list[int]:   # get the bool signature
        if s in self.bool:
            return self.bool[s]
        if self.parent is None:
            return []
        return self.parent.bool_sig(s)

    def is_bool(self, s: str) -> bool:
        return 0 in self.bool_sig(s)

    def is_lbracket(self, s: str) -> bool:
        return s in self.brackets.values() or (self.parent is not None and self.parent.is_lbracket(s))

    def is_rbracket(self, s: str) -> bool:
        return s in self.brackets.keys() or (self.parent is not None and self.parent.is_rbracket(s))

    def is_bracket(self, s: str) -> bool:
        return self.is_lbracket(s) or self.is_rbracket(s)

    def is_operator(self, s: str) -> bool:
        return self.is_prefix(s) or self.is_infix(s) or self.is_postfix(s) or self.is_bracket(s)

    def get_arity(self, fun: str) -> int:
        if fun in self.arity:
            return self.arity[fun]
        elif self.parent is not None:
            return self.parent.get_arity(fun)
        else:
            return 0

    def get_alias(self, s: str) -> Optional[str]:
        if s in self.alias:
            return self.alias[s]
        elif self.parent is not None:
            return self.parent.get_alias(s)
        else:
            return None

    def get_load_level(self, fname: str) -> Optional[int]:
        if fname in self.libs:
            return self.level
        elif self.parent is not None:
            return self.parent.get_load_level(fname)
        else:
            return None

    def add_arity(self, fun: str, a: int) -> None:
        if self.is_prefix(fun):
            raise KurtException(f'EvalError: arity of prefix operators is one and can not be set')
        if self.is_postfix(fun):
            raise KurtException(f'EvalError: arity of postfix operators is one and can not be set')
        if self.is_infix(fun):
            raise KurtException(f'EvalError: arity of infix operators is two and can not be set')
        if self.is_bracket(fun):
            raise KurtException(f'EvalError: arity of brackets can not be set')
        if fun in self.arity:
            raise KurtException(f'EvalError: arity of symbol `{fun}` has been already set to {self.arity[fun]}')
        self.arity[fun] = a

    def _find_symbol(self, op: str) -> str:
        if self.is_prefix(op):    return 'prefix'
        elif self.is_infix(op):   return 'infix'
        elif self.is_postfix(op): return 'postfix'
        elif self.is_bracket(op): return 'bracket'
        elif self.is_bindop(op):  return 'bindop'
        elif self.is_var(op):     return 'var'
        elif self.is_const(op):   return 'const'
        else: assert False, f'BUG: call "_find_symbol" only for existing symbols'

    def check_bool_sig_max(self, op: str, nargs: int) -> None:   # might raise exceptions
        bool_sig = self.bool_sig(op)
        if len(bool_sig) > 0:
            if max(bool_sig) > nargs:
                raise KurtException(f'EvalError: existing `bool` signature of `{op}` has more than {nargs} arg(s)')

    def add_prefix(self, op: str, rbp: int) -> None:
        if self.is_operator(op) and not self.is_infix(op):    # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol `{op}` already exist as {self._find_symbol(op)}')
        self.check_bool_sig_max(op, 1)
        self.prefix[op] = rbp
        self.nud[op] = lambda ts, kb, op_token: [op_token, parse_expression(ts, kb, rbp)]

    def add_infix(self, op: str, lbp: int, rbp: int) -> None:
        if self.is_operator(op) and not self.is_prefix(op):   # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol `{op}` already exist as {self._find_symbol(op)}')
        self.check_bool_sig_max(op, 2)
        self.infix[op] = (lbp, rbp)                           # to nicely list all operators
        self.led[op] = lambda ts, kb, left, op_token: [op_token, left, parse_expression(ts, kb, rbp)]
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_postfix(self, op: str, lbp: int) -> None:
        if self.is_operator(op):
            raise KurtException(f'EvalError: symbol `{op}` already exist as {self._find_symbol(op)}')
        self.check_bool_sig_max(op, 1)
        self.postfix[op] = lbp                                # to nicely list all operators
        def led(_ts: PeekableGenerator, _kb: KnowledgeBase, left: Expr, op_token: Token) -> Expr:
            return [op_token, left]
        self.led[op] = led
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_chain(self, c: list[str]) -> None:
        if len(c) != len(set(c)):
            raise KurtException(f'EvalError: all operators of a chain must be different, found duplicates in `{c}`')
        for op in c:
            if not self.is_infix(op):
                raise KurtException(f'EvalError: all operators of a chain must be infix, operator `{op}` is not')
        self.check_with_other_chains(c)
        if len(c) < 1:
            raise KurtException(f'EvalError: chain of operators must have at least one element')
        self.chain.append(c)

    def add_bindop(self, fun: str) -> None:
        if self.is_used(fun):
            raise KurtException(f'EvalError: symbol `{fun}` has been already used in a formula')
        if self.is_operator(fun):
            raise KurtException(f'EvalError: symbol `{fun}` is already used as prefix, postfix, infix, or bracket')
        if fun not in self.arity:
            raise KurtException(f'EvalError: before declaring symbol `{fun}` as variable binding, you must set its arity')
        if self.arity[fun] < 2:
            raise KurtException(f'EvalError: arity of binding operators must be at least 2')
        self.bindop.add(fun)

    def check_bool_sig_sym_flat(self, op: str) -> None:    # might raise exceptions, though
        bool_sig = self.bool_sig(op)
        # cases:
        # 1. len(bool_sig) == 0, fine
        # 2. (1 in bool_sig  iff  2 in bool_sig) and max(bool_sig) < 3
        if len(bool_sig) > 0:
            if (2 in bool_sig and 1 not in bool_sig) or (1 in bool_sig and 2 not in bool_sig):
                raise KurtException(f'EvalError: existing `bool` signature does not work for flat operator')
            if max(bool_sig) > 2:
                raise KurtException(f'EvalError: existing `bool` signature contains info for more than two args')

    def add_flat(self, op: str) -> None:
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator `{op}` must be infix operator to declare flatness')
        if self.is_flat(op):
            raise KurtException(f'EvalError: operator `{op}` is already declared "flat"')
        self.check_bool_sig_sym_flat(op)
        self.flat.add(op)

    def add_sym(self, op) -> None:
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator `{op}` must be infix operator to declare symmetry')
        if self.is_sym(op):
            raise KurtException(f'EvalError: operator `{op}` is already declared "sym"')
        self.check_bool_sig_sym_flat(op)
        self.sym.add(op)

    def add_brackets(self, lbracket, rbracket) -> None:
        if self.is_used(lbracket):
            raise KurtException(f'EvalError: symbol `{lbracket}` has been already used in a formula')
        if self.is_used(rbracket):
            raise KurtException(f'EvalError: symbol `{rbracket}` has been already used in a formula')
        if self.is_operator(lbracket) or self.is_const(lbracket) or self.is_var(lbracket):
            raise KurtException(f'EvalError: symbol `{lbracket}` already exist as {self._find_symbol(lbracket)}')
        if self.is_operator(rbracket) or self.is_const(rbracket) or self.is_var(rbracket):
            raise KurtException(f'EvalError: symbol `{rbracket}` already exist as {self._find_symbol(rbracket)}')
        self.add_const(lbracket)              # brackets must be new constants
        self.add_const(rbracket)
        self.brackets[rbracket] = lbracket    # to list the brackets (not used for parsing)
        def nud(ts: PeekableGenerator, kb: KnowledgeBase, t: Token) -> Expr:
            expr: Expr = parse_expression(ts, kb, bracket_rbp)
            token: Token = next(ts)
            if token.label == 'END':
                raise StopIteration
            if token.value != rbracket: 
                raise KurtException(f'SyntaxError: expected `{rbracket}`', column=token.column)
            token.value = f'{lbracket}$$${rbracket}'    # use a value that can not come from the tokenizer, avoid space for readability
            return [token, expr]
        self.nud[lbracket] = nud
        self.lbp[rbracket] = bracket_lbp

    def add_var(self, s: str) -> None:
        if self.is_used(s):
            raise KurtException(f'EvalError: symbol `{s}` has been already used in a formula')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol `{s}` is already used as a constant')
        self.var.add(s)

    def add_const(self, s: str) -> None:
        # a constant is automatically declared if a new symbol is used or when it is explicitly declared
        # declaring is only allowed, if it doesn't yet exist as a variable or constant
        if self.is_used(s):
            raise KurtException(f'EvalError: symbol `{s}` has been already used in a formula')
        if self.is_local_var(s):
            raise KurtException(f'EvalError: symbol `{s}` is already a variable on this level or starts with "$"')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol `{s}` is already a constant and can not be declared freshly again')
        self.const.add(s)

    def add_alias(self, s: str, t: str) -> None:
        if self.is_used(s):
            raise KurtException(f'EvalError: symbol `{s}` has been already used in a formula')
        if self.is_var(s):
            raise KurtException(f'EvalError: symbol `{s}` is already a variable or starts with $')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol `{s}` is already a constant')
        self.alias[s] = t         # add a key `s` with value `t`

    def add_bool(self, s: str, v: list[int]) -> None:
        if self.is_used(s):
            raise KurtException(f'EvalError: symbol `{s}` has been already used in a formula')
        if len(self.bool_sig(s)) > 0:
            raise KurtException(f'EvalError: symbol `{s}` is already declared bool')
        if self.is_bindop(s) and 1 in v:
            raise KurtException(f'EvalError: the first position of binding operators can not be declared boolean')
        debug(f'Adding bool signature {v} for symbol `{s}`')
        self.bool[s] = v          # add a key and set the value to the tuple of positions that are bool

    def get_nud(self, token: Token) -> Nud:
        if token.label == 'SYMBOL':
            if token.value in self.nud:
                return self.nud[token.value]
            elif self.parent is not None:
                return self.parent.get_nud(token)
        def nud(ts: PeekableGenerator, kb: KnowledgeBase, t: Token) -> Expr:
            return t
        return nud   # the default

    def get_led(self, token: Token) -> Led:
        if token.label == 'SYMBOL':
            if token.value in self.led:
                return self.led[token.value]
            elif self.parent is not None:
                return self.parent.get_led(token)
        elif token.label == 'STRING':
            def led(ts: PeekableGenerator, kb: KnowledgeBase, left: Expr, op_token: Token) -> Expr:
                return [op_token, left]
            return led              # same as for postfix
        raise KurtException(f'SyntaxError: infix or postfix operator expected, got {token.value}', token.column)

    def get_lbp(self, token: Optional[Token]) -> int:
        if token is None:
            raise StopIteration
        if token.label == 'SYMBOL':
            if token.value in self.lbp:
                return self.lbp[token.value]
            elif self.parent is not None:
                return self.parent.get_lbp(token)
        elif token.label == 'STRING':
            return string_lbp
        elif token.label == 'END':
            return end_lbp           # this is to finish the while loop in 'expression'
        # the default value
        return space_lbp             # this is used for 'f x y'

    def all_flat(self) -> Iterator[str]:
        # iterate over all levels
        for f in self.flat:
            yield f
        if self.parent is not None:
            yield from self.parent.all_flat()

    def all_chains(self) -> Iterator[list[str]]:
        for c in self.chain:
            yield c
        if self.parent is not None:
            yield from self.parent.all_chains()

    # THEORY RELATED
    def all_theory(self) -> Iterator[Formula]:
        # iterate over all levels
        for f in reversed(self.theory):
            yield f
            # can we chop of universal quantifier?
            while is_forall(f.simplified_expr):
                assert isinstance(f.simplified_expr, list) and len(f.simplified_expr) == 3
                yield f.clone(f.simplified_expr[2], self)
        if self.parent is not None:
            yield from self.parent.all_theory()

    def theory_str(self, op:Optional[str]=None, keyword:Optional[str]=None) -> str:
        s: str = self.parent.theory_str(op=op) if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.theory:
            if op is None or is_op_expr(f.expr, op):
                if keyword is None or f.keyword==keyword:
                    if self.verbose:
                        s += f'{f.formula_str(self)}   {f.simplified_expr}\n'
                    else:
                        s += f'{f.formula_str(self)}\n'
        return s

    # add new symbols and also add them to the list of symbols that are used in formulas
    # we ignore all bound vars, since they are temporary

    def add_new_symbols(self, e: Expr) -> None:
        self._add_new_bools(e, True)
        self._add_new_symbols(e, None)

    def _add_new_symbols(self, e: Expr, bound_vars: set[str]|None = None) -> None:
        if bound_vars is None:
            bound_vars = set()
        match e:
            case Token(label='SYMBOL', value=s):
                assert isinstance(s, str), f'BUG: token value must be string`'
                if self.is_var(s) or self.is_bool_var(s) or self.is_const(s):
                    pass
                elif not self.is_used(s):
                    if s not in bound_vars:
                        self.add_const(s)     # 1. add a new constant if it is not a bound var
                        self.used.add(s)      # 2. add it to the used symbols
            case [*children]:
                match children:
                    case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=v), *tail]:
                        if isinstance(op, str) and self.is_bindop(op):
                            assert isinstance(v, str), f'BUG: symbol must be string'
                            bound_vars = bound_vars | {v}   # add v to a copy of `bound_vars`
                for child in children:
                    self._add_new_symbols(child, bound_vars)
            case _:
                pass                  # do nothing, might be other tokens

    def _add_new_bools(self, e: Expr, bool_pos: bool) -> None:
        # bool_pos indicates whether the current expression is in a position that must be boolean

        # automatically infer the `bool` signature
        def _get_new_bool_sigs(e: Expr, bool_pos: bool) -> dict[str, list[int]]:
            match e:
                case Token(label='SYMBOL', value=s):
                    # case 1: just a token
                    assert isinstance(s, str), f'BUG: token value must be string'
                    if bool_pos and s[0] not in ['$', '%'] and not self.is_used(s):
                        if not self.is_bool(s):    # might be already declared as boolean
                            return {s: [0]}   # mark as boolean

                case [Token(label='SYMBOL', value=op), *args]:
                    assert isinstance(op, str), f'BUG: token value must be string'
                    bool_sigs = {}
                    bool_sig_op = self.bool_sig(op)
                    if len(bool_sig_op) > 0:
                        # case 2: operator does already exist with some boolean signature
                        for i in range(1, len(e)):
                            if self.is_flat(op):
                                bool_pos = 1 in bool_sig_op    # applies to all i
                            else:
                                bool_pos = i in bool_sig_op
                            bool_sigs |= _get_new_bool_sigs(e[i], bool_pos)
                        return bool_sigs
                    else:
                        if self.is_used(op):
                            # case 3: operator has been used already, but has no boolean signature
                            for i in range(len(args)):
                                bool_sigs |= _get_new_bool_sigs(args[i], False)
                            return bool_sigs
                        else:
                            # case 4: operator has not been used and has no boolean signature, let's try to infer its `bool` signature
                            bool_sig_local = [0] if bool_pos else []  # no recursive call for the operator itself
                            flat = self.is_flat(op)
                            sym = self.is_sym(op)
                            if flat or sym:
                                # for flat or sym operators, check whether at least one is boolean, then all are boolean
                                all_bool = False
                                for i in range(len(args)):
                                    if bool_expr(args[i], self):
                                        all_bool = True
                                        break
                                # next get all other bool signatures
                                for i in range(len(args)):
                                    bool_sigs |= _get_new_bool_sigs(args[i], all_bool)
                                bool_sigs |= {op: bool_sig_local}
                                return bool_sigs
                            else:
                                # just a normal operator
                                for i in range(len(args)):
                                    if bool_expr(args[i], self):
                                        bool_sig_local.append(i+1)    # collect information from the args
                                        bool_sigs |= _get_new_bool_sigs(args[i], True)
                                    else:
                                        bool_sigs |= _get_new_bool_sigs(args[i], False)
                                if len(bool_sig_local) > 0:
                                    # we found at least one boolean position, so we can declare the operator boolean
                                    if op[0] in '$':
                                        raise KurtException(f'EvalError: variable `{op}` appearing at boolean position, but can not be declared boolean, maybe you forgot to declare an infix/prefix/postfix operator in `{e=}`?')
                                    if op[0] in '%':
                                        raise KurtException(f'EvalError: variable `{op}` appearing at boolean operator position, but can not be an operator, maybe you forgot to declare an infix/prefix/postfix operator in `{e=}`?')
                                    bool_sigs |= {op: bool_sig_local}
                                return bool_sigs

                case [*exprs]:
                    # we don't know anything here, so just recurse
                    bool_sigs = {}
                    for e in exprs:
                        bool_sigs |= _get_new_bool_sigs(e, False)  # false, since we don't know better
                    debug(f'case 5: multiple expressions, adding bool signatures {bool_sigs}')
                    return bool_sigs

            return {}

        bool_sig = _get_new_bool_sigs(e, bool_pos)
        for s in bool_sig:
            debug(f'adding `{s}` and {bool_sig[s]}')
            self.add_bool(s, bool_sig[s])

    def theory_append(self, f: Formula, symbol_level_prev: bool = False) -> None:
        if symbol_level_prev:
            # add the symbols to the previous level
            assert self.parent is not None, f'BUG: can not add symbols one level up, check `assume` implementation'
            self.parent.add_new_symbols(f.expr)
        else:
            self.add_new_symbols(f.expr)
        self.theory.append(f)

    def show_append(self, f: Formula) -> None:
        self.add_new_symbols(f.expr)
        self.show.append(f)

    def show_str(self) -> str:
        s: str = self.parent.show_str() if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.show:
            s += f'{f.formula_str(self)}\n'
        return s

    def all_vars(self) -> set[str]:
        if self.parent is None:
            return self.var
        else:
            return self.var | self.parent.all_vars()   # set union

    def all_bool_vars(self) -> set[str]:
        if self.parent is None:
            return self.var
        else:
            return self.var | self.parent.all_bool_vars()   # set union

# create initial knowledge base and define some important constant for the parser
initial_kb: KnowledgeBase = KnowledgeBase()
begin_rbp:    int = 0                                      # right binding power of beginning of input line
end_lbp:      int = 0                                      # left  binding power of end of input line
bracket_rbp:  int = 1                                      # right binding power of left brackets
bracket_lbp:  int = 1                                      # left  binding power of right brackets
initial_kb.add_brackets('(', ')')                          # round brackets for grouping
string_lbp:   int = 2                                      # left  binding power of strings
initial_kb.add_infix (COMMA_SYMBOL, 5, 5)                  # comma   is infix operator
initial_kb.add_infix (IMPL_SYMBOL, 13, 12)                 # implies is infix operator
initial_kb.add_infix (AND_SYMBOL, 16, 16)                  # and     is infix operator
space_lbp:    int = 22                                     # left  binding power: stronger than '=' (defined in equality.kurt)
space_rbp:    int = 22                                     # right binding power: stronger than '=' (defined in equality.kurt)
initial_kb.add_infix (SPACE_SYMBOL, space_lbp, space_rbp)  # space op is for fn like `f x`

initial_kb.add_bool  (TRUE_SYMBOL, [0])                    # true is bool
initial_kb.add_bool  (IMPL_SYMBOL, [0, 1, 2])              # implies is bool with bool input
initial_kb.add_bool  (AND_SYMBOL,  [0, 1, 2])              # and is bool with bool inputs
initial_kb.add_const (TRUE_SYMBOL)                         # true is const symbol
initial_kb.add_const (IMPL_SYMBOL)                         # implies is const symbol
initial_kb.add_const (AND_SYMBOL)                          # and is const symbol
initial_kb.add_flat  (COMMA_SYMBOL)                        # comma op is flat
initial_kb.add_flat  (AND_SYMBOL)                          # and is flat
initial_kb.add_sym   (AND_SYMBOL)                          # and is symmetric
initial_kb.add_arity (SUB_SYMBOL, 3)                       # sub takes three args
initial_kb.add_bindop(SUB_SYMBOL)                          # sub is a binding operator
initial_kb.add_alias('⊤', TRUE_SYMBOL)                     # alias for true
initial_kb.add_alias('⇒', IMPL_SYMBOL)                     # alias for implies
initial_kb.add_alias('∧', AND_SYMBOL)                      # alias for implies

################
## kurt lexer ##
################

## expressions
# an expression is either a token or a list of expressions
# instead of creating a class for expressions, we use the following functions

def expr_str(expr: Expr, kb: KnowledgeBase) -> str:
    if kb.format == 'sexpr':
        return expr_sexpr(expr)
    elif kb.format == 'normal':
        s: str = expr_normal(expr, kb)
        if len(s) > 0  and  s[0] == '(' and s[-1] == ')':
            s = s[1:-1]         # the brackets are useful during construction, but on the top level we have to omit them
        return s
    else:
        assert False, f'BUG: unknown expression format, got {kb.format}'

def expr_sexpr(expr: Expr) -> str:                      # create s-expression
    match expr:
        case Token(label='STRING', value=v):
            return f'"{v}"'       # quotation marks
        case Token(value=v, origin=origin):
            if origin is None:
                return str(v)
            else:
                return str(origin)
        case [*entries]:
            return f'({" ".join([expr_sexpr(e) for e in entries])})'
    assert False, f'BUG: unknown expression, got {expr_str(expr, kb)}'

def expr_normal(expr: Expr, kb: KnowledgeBase, rbp: int=0) -> str:          # create raw input expression
    match expr:
        case Token():
            return expr_sexpr(expr)            # reuse implementation from expr_sexpr
        case [e0]:
            return expr_normal(e0, kb)
        case [Token(label='SYMBOL', value=a), e1] if isinstance(a, str) and kb.is_prefix(a):
            return f'({expr_normal(expr[0], kb)} {expr_normal(e1, kb)})'
        case [Token(label='SYMBOL', value=a), e1] if isinstance(a, str) and kb.is_postfix(a):
            return f'({expr_normal(e1, kb)} {expr_normal(expr[0], kb)})'
        case [e0, e1]:
            return f'{expr_normal(e0, kb)} {expr_normal(e1, kb)}'
        case [Token(label='SYMBOL', value=a), e1, e2] if isinstance(a, str) and kb.is_infix(a):
            return f'({expr_normal(e1, kb)} {expr_normal(expr[0], kb)} {expr_normal(e2, kb)})'
        case [Token(label='SYMBOL', value=a), e1, e2]:
            return f'({expr_normal(expr[0], kb)} {expr_normal(e1, kb)} {expr_normal(e2, kb)})'
        case [Token(label='SYMBOL', value=a), *tail] if isinstance(a, str) and kb.is_flat(a):
            return f'({f" {expr_normal(expr[0], kb)} ".join([expr_normal(e, kb) for e in tail])})'
        case [*tail]:
            return f'({" ".join([expr_normal(e, kb) for e in tail])})'
    assert False, f'BUG: unknown expression, got {expr_str(expr, kb)}'

def is_op_expr(e: Expr, op: str) -> bool:
    match e:
        case [Token(label='SYMBOL', value=v), *_]:
            return v == op
        case _:
            return False

def is_implication(expr: Expr) -> bool:
    return is_op_expr(expr, IMPL_SYMBOL)

def is_not(expr: Expr) -> bool:
    return is_op_expr(expr, NOT_SYMBOL)

def is_forall(expr: Expr) -> bool:
    return is_op_expr(expr, FORALL_SYMBOL)

def is_exists(expr: Expr) -> bool:
    return is_op_expr(expr, EXISTS_SYMBOL)

def is_equality(expr: Expr) -> bool:
    return is_op_expr(expr, EQUAL_SYMBOL)

def is_iff(expr: Expr) -> bool:
    return is_op_expr(expr, IFF_SYMBOL)

def is_comma_separated_list(expr: Expr) -> bool:
    return is_op_expr(expr, COMMA_SYMBOL)

def equal_expr(t1: Expr, t2: Expr) -> bool:                                     # equality for expressions
    # note: we assume that `flatness` and `symmetry` has been used to create normalized form
    if isinstance(t1, Token) and isinstance(t2, Token):                         # compare tokens
        return t1.label==t2.label and t1.value==t2.value
    elif isinstance(t1, list) and isinstance(t2, list) and len(t1)==len(t2):    # compare lists
        return all([equal_expr(a, b) for (a,b) in zip(t1, t2)])
    else:                                                     # token and list are always non-equal
        return False

def first_var(expr: Expr, kb: KnowledgeBase) -> str:
    match expr:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and not kb.is_var(s):
            return s
        case [head, *tail]:
            return first_var(head, kb)
        case _:
            assert False, 'empty expression?'

# special tokens that are made for the parser and sometimes artificially generated
space_token: Token = Token('SYMBOL', SPACE_SYMBOL)  # for expressions like 'f x'
end_token:   Token = Token('END', '$$$')            # for the end of a string
todo_token:  Token = Token('TODO', '')              # for empty todo expressions

# extract all special symbols from the replacement values
SPECIAL_SYMBOLS = ''.join(sorted(set(''.join(REPLACEMENTS.values()))))

# scanner based on regular expressions (let's support unicode!)
# note that the ordering of the expressions here is important
scanner: re.Pattern = re.compile(fr'''
  (?P<LOAD>(?i:load)\s+(?P<LOAD_BODY>[^\n;]*))    | # captures everything after `load` up to ';' or EOL
  (?P<COMMENT> [;].*$)                            | # comments
  (?P<FLOAT>   [0-9]+\.[0-9]+)                    | # floating point literals
  (?P<INT>     [0-9]+)                            | # integer literals
  (?P<STRING>  ["][^"]*["])                       | # string literals
  (?P<SYMBOL>  [$%@]?[A-Za-z][A-Za-z0-9]*         | # symbols 1: identifiers with at most one leading '$' or '%' or '@'
               [()]                               | # symbols 2: round brackets
               [,]                                | # symbols 3: comma
               [.:=+\-*/#&^'∈!<>{{}}[\]|_]+       | # symbols 4: standard operators including literal {{ }}
               [{re.escape(SPECIAL_SYMBOLS)}])    | # symbols 5: logic, Greek and other math symbols (always single char)
  (?P<NEWLINE> [\n])                              | # newline
  (?P<WHITE>   [^\S\n\r]+)                        | # whitespace (not newline)
  (?P<ERROR>   .)                                 # anything else is an error
''', re.VERBOSE | re.MULTILINE)

# filename magic
filenames_pattern = re.compile(r'''
    \s*                 # optional leading spaces
    (?:                 # either...
        "([^"]*)"       # 1. quoted filename (capture without quotes)
      | ([^",\s][^,\s]*)# 2. unquoted filename (no spaces/commas)
    )
    \s*                 # optional trailing spaces
    (?:,|$)             # followed by comma or end
''', re.VERBOSE)

def split_filenames(s: str) -> list[str]:
    out = []
    for m in filenames_pattern.finditer(s):
        quoted, unquoted = m.groups()
        val = quoted if quoted is not None else unquoted
        if val:
            out.append(val)
    return out

# notes:
# since we are using an `f-string` for the regex, we have to escape the curly brackets
# common white space:
# \t tab
# \n newline
# \r carriage return
# \f form feed
# \v vertical tab

def scan_string(input_line: str, kb: KnowledgeBase) -> Iterator[Token]:

    # setup current location
    lastpos: int = 0        # for calculating the column number, update after a newline
    for match in scanner.finditer(input_line):
        
        # extract the information from the match
        assert match.lastgroup is not None
        label:  str   = match.lastgroup           # name of the group
        value:  Value = match.groupdict()[label]  # the value, somewhat complicated code, but necessary for counting the indents
        pos:    int   = match.start()             # position in s
        column: int   = pos - lastpos             # column of the match

        # create tokens
        if   label == 'COMMENT':           # remove leading semicolon and space at beginning and end
            continue
        elif label == 'WHITE':
            continue                       # whitespace is ignored
        elif label == 'SYMBOL':
            assert isinstance(value, str)
            alias:  Optional[str] = kb.get_alias(value)
            origin: Optional[str] = None
            if alias is not None:
                origin = value             # store for string generation
                value  = alias
            yield Token(label, value, column + len(value), origin)
        elif label == 'INT':
            yield Token(label, int(value), column + len(str(value)))
        elif label == 'FLOAT':
            yield Token(label, float(value), column + len(str(value)))
        elif label == 'STRING':
            assert isinstance(value, str)
            yield Token(label, value[1:-1], column + len(value))
        elif label == 'NEWLINE': 
            assert False, f'BUG: newlines not allowed in "input_line"'
        elif label == 'LOAD':
            body = match.group('LOAD_BODY')
            yield Token('SYMBOL', 'load', column + 4)
            names = split_filenames(body)
            for i, name in enumerate(names):
                yield Token('STRING', name, column + 4 + len(name))
                if i < len(names) - 1:
                    yield Token('SYMBOL', COMMA_SYMBOL, column + 4 + len(name))
        elif label == 'ERROR':  # error
            raise KurtException(f'SyntaxError: scanning error while scanning `{value}`', column)
        else:
            assert False, f'BUG: unknown label, got {label}'
    yield end_token

#################
## kurt parser ##
#################
# Pratt style
# following https://web.archive.org/web/20150228044653/http://effbot.org/zone/simple-top-down-parsing.htm
# more links:
# https://web.archive.org/web/20150218020849/http://javascript.crockford.com/tdop/tdop.html
# https://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/
# https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html

# continuation tokens: infix, postfix, closing brackets, space_token (which is infix as well)
def is_led_token(token: Token, kb: KnowledgeBase) -> bool:
    if token.label == 'SYMBOL':
        op = token.value
        assert isinstance(op, str)
        return kb.is_infix(op) or kb.is_postfix(op) or kb.is_rbracket(op)
    elif token.label == 'STRING':
        return True                  # this case is for handling the strings that give labels to formulas
    else:
        return False

# starting tokens: prefix, opening brackets, bindop, numbers, strings (labels), etc
def is_nud_token(token: Token, kb: KnowledgeBase) -> bool:
    if token.label == 'SYMBOL':
        op = token.value
        assert isinstance(op, str)
        # these checks are necessary, since, e.g., `-` can be both prefix and infix
        if kb.is_prefix(op) or kb.is_lbracket(op) or kb.is_bindop(op):
            return True
        else:
            return not is_led_token(token, kb)  # if not infix/postfix, then it is a number or string
    else:
        return True

# the heart of the Pratt parser (calls 'led' and 'nud' implemented in various versions)
def parse_expression(ts: PeekableGenerator, kb: KnowledgeBase, rbp: int) -> Expr:
    t: Token = next(ts)                           # get next token
    if not is_nud_token(t, kb):
        raise KurtException(f'SyntaxError: token `{t.value}` cannot start an expression', t.column)
    nud: Nud = kb.get_nud(t)                      # get the correct 'nud' function
    left: Expr = nud(ts, kb, t)                   # nud == "null denotation"
    peek_lbp: int = kb.get_lbp(ts.peek)           # peek at lbp of the next token
    while rbp < peek_lbp:                         # is the next operator binding more strongly?
        if peek_lbp == space_rbp:                 # not another operator but another expression
            t: Token = space_token                # insert special token for expression like 'f x'
        else:                                     # peek_lbp is larger or smaller than space_rbp
            t: Token = next(ts)                   # get next token
        led: Led = kb.get_led(t)                  # get the correct 'led' function
        left: Expr = led(ts, kb, left, t)         # led == "left denotation"
        peek_lbp: int = kb.get_lbp(ts.peek)       # update peek_lbp for the iteration
    return left                                   # return the accumulated expression

def canonical_key(t: Expr, s: State, kb: KnowledgeBase) -> tuple:
    # head-normalize under current σ and scope
    t = s.walk(t)

    if isinstance(t, Token):
        val = t.value
        is_var = isinstance(val, str) and (kb.is_var(val) or kb.is_bool_var(val))
        # Normalize the value for sorting (avoid mixing types)
        val_key = ('S', val) if isinstance(val, str) else ('O', repr(val))
        # Order: constants (0) < variables (1)
        return (0 if not is_var else 1, 'T', t.label, val_key)

    if isinstance(t, list):
        # Recurse to see deeper substitutions in children
        head_key = canonical_key(t[0], s, kb) if t else ('Z',)
        child_keys = tuple(canonical_key(c, s, kb) for c in t[1:])
        # Lists after atoms
        return (2, 'L', head_key, len(t) - 1, child_keys)

    # Fallback (shouldn’t normally happen)
    return (3, 'Z', repr(t))

def sort_exprs(exprs: list[Expr], s: State, kb: KnowledgeBase) -> list[Expr]:
    return sorted(exprs, key=lambda e: canonical_key(e, s, kb))

def symmetrize_all(expr: Expr, kb: KnowledgeBase) -> Expr: # symmetric operators can sort their args
    ignore = [EQUAL_SYMBOL, IFF_SYMBOL] # we never sort the args of `=` and `iff`, because that would break `def` which requires LHS and RHS to be in a certain order
    if isinstance(expr, list):
        expr = [symmetrize_all(e, kb) for e in expr] # start inside
        if (isinstance(expr[0], Token) 
            and expr[0].label == 'SYMBOL' 
            and isinstance(expr[0].value, str) 
            and kb.is_sym(expr[0].value) 
            and expr[0].value not in ignore):
            s = State.empty()  # empty substitution and no bound vars
            expr = [expr[0]] + sort_exprs(expr[1:], s, kb)  # sort args of symmetric operator
        return expr
    elif isinstance(expr, Token):
        return expr
    else:
        assert False, f'BUG: expression must be list or Token, got {expr_str(expr, kb)}'

def flatten_op(flat_op: str, expr: Expr) -> Expr:  # flatten nested 'op'-expressions
    # e.g. [',', 17, [',', 42, 100]] --> [',', 17, 42, 100]
    match expr:
        case [Token(label='SYMBOL', value=op), *tail] if op==flat_op:
            e: Expr = [expr[0]]
            for child in tail:
                ee: Expr = flatten_op(flat_op, child)
                if is_op_expr(ee, flat_op):
                    assert isinstance(ee, list) and len(ee) > 1
                    e.extend(ee[1:])
                else:
                    e.append(ee)
            return e
        case [*_]:
            return [flatten_op(flat_op, e) for e in expr]
        case Token():
            return expr
    assert False, f'BUG: expression must be list or Token, got {expr_str(expr, kb)}'

def flatten_all(expr: Expr, kb: KnowledgeBase) -> Expr:
    for op in kb.all_flat():
        expr = flatten_op(op, expr)       # flatten certain operators
    return expr

def group_by_arity(expr: Expr, kb: KnowledgeBase) -> tuple[Expr, list[Expr]]:
    # input: `expr` which is a list of functions and arguments
    # output: `e` which is properly group and the `tail` which is the rest of non-eaten arguments
    match expr:
        case [Token(label='SYMBOL', value=op), *tail] if isinstance(op, str) and ((arity:=kb.get_arity(op)) > 0):
            e: Expr = [expr[0]]                                       # the new expression
            for i in range(1, arity+1):
                if len(tail) == 0:
                    raise KurtException(f'EvalError: not enough arguments for `{op}`')
                ei: Expr
                tail: list[Expr]
                ei, tail = group_by_arity(tail, kb)             # let the next one eat as many expr as it needs
                e.append(ei)
            return e, tail
        case [head, *tail]:        # list with operator that doesn't have an arity > 0
            return head, tail
        case _:
            assert False, f'BUG: `group_by_arity` must be called with a list of expressions'

def process_arity(expr: Expr, kb: KnowledgeBase) -> Expr:
    # we assume that `flatten_op` for `op=' ' has been called just before
    # calls `group_by_arity` for each ' ' operator
    match expr:
        case Token():
            return expr
        case [Token(label='SYMBOL', value=v), *tail] if v==SPACE_SYMBOL:
            expr, tail = group_by_arity(tail, kb)
            if len(tail) > 0:
                expr = [expr] + tail         # extra arguments (might be there for keywords!)
    assert isinstance(expr, list)
    return [process_arity(e, kb) for e in expr]

def remove_round_brackets(expr: Expr) -> Expr:
    match expr:
        case Token():
            return expr
        case [Token(label='SYMBOL', value='($$$)'), sub_expr]:
            return remove_round_brackets(sub_expr)
        case [*list_expr]:
            return [remove_round_brackets(e) for e in list_expr]
        case _:
            assert False, f'BUG: list or Token expected, got {expr_str(expr, kb)}'

def is_helper_keyword(e: Expr) -> bool:
    return isinstance(e, Token) and e.value in helper_keywords

def check_for_helper_keywords(e: Expr, top_level:bool = True):
    # helper keywords can only appear on the top level
    if isinstance(e, list):
        for ei in e:
            if not top_level and is_helper_keyword(ei):
                raise KurtException(f'ParseError: helper keywords like `{ei}` are only allowed on the top level')
            check_for_helper_keywords(ei, False)

def check_no_keyword(expr: Expr, top_level:bool = True) -> None:
    match expr:
        case Token(label='SYMBOL', value=v) if v in keywords:
            raise KurtException(f'SyntaxError: keywords not allowed inside expressions', expr.column)
        case Token(label='SYMBOL', value=v) if v in helper_keywords and not top_level:
            raise KurtException(f'SyntaxError: keywords not allowed inside expressions', expr.column)
        case [*_]:
            for e in expr:
                check_no_keyword(e)
        case _:
            pass

def check_expr_label(expr: Expr, kb) -> tuple[Expr, str]:            # check [expr] [label]
    # cases:
    #   x=9  "eq 1"
    #   true
    #   x=9
    label = ''
    match expr:
        case [Token(label='STRING', value=label), *tail]:  # labels are parsed like very low binding postfix operators
            assert isinstance(label, str)
            if len(tail) == 1:
                tail = tail[0]
        case [*tail]:
            if len(tail) == 1:
                tail = tail[0]
        case Token():
            tail = expr
        case _:
            assert False, f'BUG: list or Token expected, got {expr_str(expr, kb)}'
    return tail, label

def post_process(kb: KnowledgeBase, expr: Expr) -> tuple[Expr, str]:
    expr = flatten_op(SPACE_SYMBOL, expr)               # flatten all space operators
    expr = process_arity(expr, kb)                      # turns space operators into function calls according to arities
    expr = remove_round_brackets(expr)                  # remove round brackets for grouping
    expr, label = check_expr_label(expr, kb)       # check and split `expr` and `label`
    expr = flatten_all(expr, kb)                        # flatten `flat` operators
    expr = symmetrize_all(expr, kb)                     # symmetrize `sym` operators
    return expr, label

def parse_tokenstream(ts: PeekableGenerator, kb: KnowledgeBase) -> tuple[Optional[Token], list[Expr], str]:
    assert isinstance(ts.peek, Token)
    keyword_token: Optional[Token] = None
    keyword: str = ''
    label: str = ''
    if ts.peek.label == 'SYMBOL' and ts.peek.value in keywords:
        keyword = ts.peek.value
        keyword_token = next(ts)                              # remove a keyword right away early
    if ts.peek.label == 'END': 
        return keyword_token, [], ''                          # empty token stream
    expr_list: list[Expr]
    if keyword_token is None or keyword_token.value in keywords_with_parsing:
        expr: Expr  = parse_expression(ts, kb, begin_rbp)     # parse expression
        expr, label = post_process(kb, expr)                  # turn spaces into calls, symmetry, flatness
        expr_list = chop_off_comma(expr)
        check_for_helper_keywords(expr_list)    # `with` is only allowed on top level
        check_no_keyword(expr_list)             # keywords are not allowed in expressions
        if keyword == 'thus':
            # type check with the parent
            if kb.parent is None:
                raise KurtException(f'EvalError: "thus" can only be used after "fix", "take", or "assume"')
            kb = kb.parent
        try:
            type_check_expression(expr, kb)                       # (some) type checking
        except KurtException as e:
            if keyword_token in ['parse']:
                print(f'type check failed', file=sys.stderr)
            else:
                print(f'parsed as: {expr_str(expr, kb)}', file=sys.stderr)
                raise e      # reraise it
    else:
        expr_list = split_by_comma(list(ts)[:-1])             # [:-1] removes end_token
        check_no_keyword(expr_list)             # don't check the `keyword` and the `label`
    return keyword_token, expr_list, label

## kurt eval
def create_usage(keyword: str, arg_labels: list[list[Label]]) -> str:
    s: str = ''
    for arg_label in arg_labels:
        s += f'    {keyword}'
        for l in arg_label:
            s += f' {l}'
        s += f'\n'
    return s

def strip_keyword(s: str, column: int) -> str:
    return s[(1+column):]                  # get rid of the keyword at the beginning

# create a good reference string for a formula `f`
def formula_ref(f: Formula, filename: str, mainstream: bool) -> str:
    if mainstream and f.filename==filename:
        return f'{f.line}' if len(f.label)==0 else f'"{f.label}"'
    else:
        return f'{os.path.basename(f.filename)}:{f.line}' if len(f.label)==0 else f'"{f.label}"'

def decorate_reason(mainstream: bool, reason: str, filename: str, line_str: str) -> str:
    if mainstream:
        return f'{line_str} {reason}'
    else:
        return f'{os.path.basename(filename)}:{line_str} {reason}'

def increase_level(kb:KnowledgeBase, mode: Mode) -> KnowledgeBase:
    return KnowledgeBase(parent=kb, mode=mode)

def decrease_level(kb:KnowledgeBase) -> KnowledgeBase:
    if kb.level == 0:
        raise KurtException(f'EvalError: no block to close')
    if len(kb.show) > 0:                  # any planned formulas inside the current proof?
        raise KurtException(f'ProofError: planned formula `{expr_str(kb.show[-1].expr, kb)}` in current proof is unproven')
    assert kb.parent is not None, f'BUG: we should be one level up'
    return kb.parent                        # drop current level

def eval_use(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool, keyword: str) -> Formula:
    if not bool_expr(expr, kb, strict=False):    # not strict, since we are possibly adding new symbols
        raise KurtException(f'EvalError: must evaluate to boolean, got `{expr_str(expr, kb)}`')
    reason = 'without proof'
    if len(label) > 0:
        reason += f' "{label}"'
    reason = decorate_reason(mainstream, reason, filename, str(line))
    return Formula(kb, expr, str(line), filename, label, reason, keyword)

def eval_show(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    if not bool_expr(expr, kb, strict=False):   # not strict, since we are possibly adding new symbols
        raise KurtException(f'EvalError: must evaluate to boolean, got `{expr_str(expr, kb)}`')
    reason = decorate_reason(mainstream, 'claim', filename, str(line))
    if len(label) > 0:
        reason += f' "{label}"'
    f = Formula(kb, expr, str(line), filename, label, reason, keyword='show')
    kb.show_append(f)
    if mainstream:
        log(f'show {expr_str(expr, kb)}', reason, kb.level)
    return kb

def eval_proof(kb: KnowledgeBase, mainstream: bool) -> KnowledgeBase:
    if len(kb.show) == 0:
        raise KurtException(f'ProofError: can not start proof since there is no planned formula on current level')
    if mainstream:
        log('proof', '', kb.level)
    kb = increase_level(kb, ('proof', []))          # add a new level/scope to the knowledgebase
    return kb

# def
# LHS: exactly one unused symbol that is not a variable or boolean variable
def eval_def(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool) -> tuple[Formula, str]:
    match expr:
        case [Token(label='SYMBOL', value=s), LHS, RHS] if isinstance(s, str) and (s== EQUAL_SYMBOL or s==IFF_SYMBOL):
            lhs_candidates = extract_by_condition(LHS, lambda s: not kb.is_const(s) and not kb.is_var(s) and not kb.is_bool_var(s))
            if len(lhs_candidates) != 1:
                raise KurtException(f'EvalError: `def` requires exactly one new constant on the left-hand side, got `{lhs_candidates}` in `{expr_str(expr, kb)}`')
            lhs_const = lhs_candidates[0]
            rhs_candidates = extract_by_condition(RHS, lambda s: not kb.is_const(s) and not kb.is_var(s) and not kb.is_bool_var(s))
            if len(rhs_candidates) != 0:
                raise KurtException(f'EvalError: `def` does not allow new symbols on the right-hand side, got `{rhs_candidates}` in `{expr_str(expr, kb)}`')
        case _:
            raise KurtException(f'EvalError: `def` only allowed with `{EQUAL_SYMBOL}` and `{IFF_SYMBOL}`, got `{expr_str(expr, kb)}`')
    return eval_use(kb, expr, label, filename, line, keyword='def', mainstream=False), lhs_const

def eval_openblock(kb: KnowledgeBase, mode: Mode, line: int, mainstream: bool) -> KnowledgeBase:
    if mainstream:
        reason = f'{line} open local scope'
        log('openblock', reason, kb.level)
    kb = increase_level(kb, mode)          # add a new level/scope to the knowledgebase
    return kb

def contains_bool_vars(expr: Expr, kb: KnowledgeBase) -> bool:
    # check whether the expression contains any boolean variables
    match expr:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and kb.is_bool_var(s):
            return True
        case [*children]:
            return any(contains_bool_vars(c, kb) for c in children)
        case _:
            return False

def contains(expr: Expr, symbols: set[str], kb: KnowledgeBase) -> bool:
    # check whether the `expr` contains certain `symbols`
    # note that bound variables are ignored
    match expr:
        # symbols
        case Token(label='SYMBOL', value=s):
            assert isinstance(s, str)
            return s in symbols
        # binding operator
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bound_v), *tail] if isinstance(op, str) and kb.is_bindop(op):
            assert isinstance(bound_v, str)
            symbols_wo_bound_v = symbols - {bound_v}  # set difference creating a new set
            return contains(tail, symbols_wo_bound_v, kb)
        # other list
        case [*children]:
            return any(contains(c, symbols, kb) for c in children)
        case _:
            return False

def eval_thus(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    # `thus` is closing a block opened by `assume`, `fix` and `pick`
    # but also for `not-intro`, `forall-intro`, `impl-intro`, `exists-elim`

    # check that there are no constant symbols on this level appearing in `expr`
    # (1) for `assume` (not-intro and impl-impl) create new constants already on the level below
    # (2) for `fix` (forall-intro) and `pick` (exists-elim) create new constants on the new level

    # the constants on the current level are not allowed, however, the variables of the previous level are allowed (see `de-morgan.kurt`)
    assert kb.parent is not None
    kb_parent = kb.parent
    not_allowed = set(filter(lambda s: not kb_parent.is_bool_var(s) and not kb_parent.is_var(s), kb.const))
    if contains(expr, not_allowed, kb):
        raise KurtException(f'ProofError: there are constant symbols on the current level appearing in the conclusion of `thus`, got `{expr_str(expr, kb)}`')

    # try to derive `expr` depending on its form and on the mode of the current level
    # these calls might generate exceptions
    match kb.mode_str:
        case 'assume':      # impl-intro or not-intro
            if is_not(expr):
                reason = not_intro(expr, kb)
            elif is_implication(expr):
                reason = impl_intro(expr, kb)
            else:
                raise KurtException(f'ProofError: current block opened by `assume` but conclusion of `thus` is neither negation nor implication, got `{expr_str(expr, kb)}`')
        case 'fix':         # forall-intro
            n_fv = len(free_vars_only(expr, kb_parent))
            n_fv_bool = len(free_bool_vars_only(expr, kb_parent))
            if is_forall(expr) or n_fv > 0 or n_fv_bool > 0:
                reason = forall_intro(expr, kb, filename, mainstream)
            else:
                raise KurtException(f'ProofError: current block opened by `fix` but conclusion of `thus` is neither universal quantification nor contains free variables, got `{expr_str(expr, kb)}`')
        case 'pick':        # exists-elim
            reason = exists_elim(expr, kb, filename, mainstream)

    # add a the new formula to the theory
    reason = decorate_reason(mainstream, reason, filename, str(line))
    label = ''
    f = Formula(kb, expr, str(line), filename, label, reason, keyword='')
    kb = decrease_level(kb)                    # drop current level and perform some checks
    kb.theory_append(f)                        # add a copy to the theory
    if mainstream:
        log('thus ' + f.formula_str(kb), reason, kb.level)
    return kb

def _first_or_none(xs: Iterator[State]) -> Optional[State]:
    return next(iter(xs), None)

def eval_qed(kb: KnowledgeBase, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    parent = kb.parent
    if not kb.mode_str == 'proof'  or  parent is None:
        raise KurtException(f'EvalError: no proof to finish, `qed` can only appear at the end of a `proof` block')
    assert len(parent.show) > 0, f'BUG: no planned formula on previous level, this should have been already checked when calling "proof"'
    planned_f = parent.show[-1]
    planned_expr = planned_f.simplified_expr        # peek at the last planned formula from previous level
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: no formula has been proven, `qed` can only be used after a successful proof')
    proven_f = kb.theory[-1]               # check the last formula
    proven_expr  = proven_f.simplified_expr         # what actually has been proven
    if proven_expr == todo_token:
        reason = f'by a miracle'
        if mainstream:
            log('todo', reason, kb.level)
        label = ''
    else:
        reason = ''
        # block all free variables of the planned expression, since they are universally quantified
        blocked_as_domain = frozenset(free_vars_only(planned_expr, kb))
        s = State({}, blocked_as_domain, frozenset())
        optional_s = _first_or_none(unify_exprs_with_patterns([(planned_expr, proven_expr)], s, kb))
        if optional_s is None:
            raise KurtException(f'ProofError: planned formula `{planned_expr}` does not match the last formula in the theory `{proven_expr}`')
        reason = decorate_reason(mainstream, reason, filename, str(line))
        label = ''
    f = Formula(kb, planned_f.expr, str(planned_f.line), filename, label, reason, keyword='')
    kb = decrease_level(kb)                    # drop current level and perform some checks
    kb.show.pop()                              # pop the last planned formula off the show stack, since it is proved now
    kb.theory_append(f)                        # add a copy to the current theory
    if mainstream:
        log('qed', '', kb.level)
        #log(f.formula_str(kb), reason, kb.level)
    return kb

def is_new_symbol_or_existing_variable(s: str, kb: KnowledgeBase) -> bool:
    return kb.is_var(s) or kb.is_bool_var(s) or not kb.is_used(s)

def extract_by_condition(e: Expr, c: Callable[[str], bool]) -> list[str]:
    match e:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and c(s):
            return [s]        # new string fulfilling the condition
        case [*children]:
            found = []
            for child in children:
                found += extract_by_condition(child, c)
            return found
    return []

# what is allowed for `fix`?
#     fix x      ; x must be new constant or existing variable
#     fix x>0    ; x must be new constant or existing variable
# in the block that is opened, `x` will be constant
# `x` can not be an existing constant
def eval_fix(kb: KnowledgeBase, expr: Expr, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    with_condition = isinstance(expr, list) and bool_expr(expr, kb)
    new_consts = extract_by_condition(expr, lambda s: is_new_symbol_or_existing_variable(s, kb))
    if len(new_consts) != 1:
        raise KurtException(f'EvalError: expected exactly one new symbol or existing, got {new_consts} in `{expr_str(expr, kb)}`')
    new_const = new_consts[0]
    kb.add_const(new_const)          # add the new constant to the knowledgebase
    if with_condition:
        f = eval_use(kb, expr, 'fix', filename, line, keyword='use', mainstream=False)  # use the expression as an assumption
        kb.theory_append(f)
    return kb

def eval_pick(kb: KnowledgeBase, new_const_expr: Expr, fact_expr: Expr, filename: str, line: int, mainstream: bool) -> tuple[KnowledgeBase, Expr]:
    assert isinstance(new_const_expr, Token) and new_const_expr.label=='SYMBOL'
    new_const = new_const_expr.value
    assert isinstance(new_const, str)

    # (1) parse `fact_expr`
    if not isinstance(fact_expr, list):
        fact_expr = [fact_expr]
    tokenlist: Expr = fact_expr + [end_token]                          # add end token for parse_expression
    ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))  # turn list into peekable generator
    fact = parse_expression(ts, kb, begin_rbp)     # parse the tokenlist
    fact, label = post_process(kb, fact)      # turn spaces into calls, symmetry, flat space operators

    # (2) check that the `fact` matches some existential statement in the theory so far
    for candidate in kb.all_theory():
        cand_expr = candidate.simplified_expr
        if is_exists(cand_expr):
            match cand_expr:
                case [Token(label='SYMBOL', value=quantifier), Token(label='SYMBOL', value=bound_var), body] if isinstance(bound_var, str):
                    assert quantifier == EXISTS_SYMBOL
                    s = State({bound_var: new_const_expr}, frozenset(), frozenset())
                    body = deepcopy_expr(body)
                    body = apply_subst(body, s, kb)
                    if equal_expr(body, fact):
                        break  # end the loop without the `else` block
    else:
        raise KurtException(f'ProofError: can not find an existential formula that matches the `pick`')

    # (3) open a new block, add a new constant and the fact
    kb = eval_openblock(kb, ('pick', new_const_expr), line, mainstream=False);    # open a new block
    kb.add_const(new_const)                            # add the new constant to the knowledgebase
    reason = f'added as a fact for witness `{new_const}`'
    f = Formula(kb, fact, str(line), filename, label, reason, keyword='')
    kb.theory_append(f)
    return kb, fact

def eval_keyword_expression(keyword_token: Token, args: Expr, label: str, kb: KnowledgeBase, line: int, filename: str, mainstream: bool) -> KnowledgeBase:
    keyword = keyword_token.value
    assert isinstance(keyword, str)
    assert isinstance(args, list)

    # GENERAL STUFF
    if keyword == 'help':
        for k in keywords.keys(): print(f'  {k:<12} {keywords[k]}', file=sys.stdout)
    elif keyword == 'load':
        current_path: str = os.path.split(filename)[0]    # search first at the current path
        local_path = theory_path
        if len(current_path) > 0:
            local_path = [current_path] + local_path
        if len(args) == 0:
            raise KurtException(f'ParseError: `{keyword}` takes at least one filename or several comma-separated', keyword_token.column)
        debug(f'loading {len(args)} files')
        debug(f'{args}')
        for arg in args:
            assert isinstance(arg, list) and len(arg) == 1, f'BUG: `load` expects [[fname1], [fname2]]'
            match arg[0]:
                case Token(label='STRING', value=fname):
                    assert isinstance(fname, str)
                    kb = load_file(fname, kb, path=local_path, mainstream=False)
                case _:
                    assert False, f'BUG: `load` was scanned with wrong args'
    elif keyword == 'parse':
        if len(args) > 0:
            msg = '; sexpr\n'
            for args_i in args:
                msg += f'{expr_sexpr(args_i)}, '
            msg = msg[:-2] + '\n' # remove last ', ' and add newline
            msg += '; syntax info'
            for args_i in args:
                tokens = get_token_set(args_i)
                info = ''
                for t in tokens:
                    info += '\n' + kb.info(t)
            info = '\n'.join(sorted([line for line in info.split('\n') if len(line) > 0]))
            msg += f'\n{info}'
            print(msg, file=sys.stdout)
    elif keyword == 'tokenize':
        if len(args) > 0:
            msg = ''
            for args_i in args:            
                tokenlist: Expr = args + [end_token]                               # add end token for parse_expression
                ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))  # turn list into peekable generator
                msg += f'{"  ".join([str(t) for t in ts])}'
            print(msg, file=sys.stdout)
    elif keyword == 'format':
        match args:
            case []:
                print(kb.format, file=sys.stdout)
            case [[Token(label='SYMBOL', value=option)]] if option in format_options:
                kb.format = option
            case _:
                raise KurtException(f'only a single arg out of {format_options} is allowed"')
    elif keyword == 'level':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        print(kb.level, file=sys.stdout)
    elif keyword == 'mode':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        print(kb.mode_str, file=sys.stdout)
    elif keyword == 'trail':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        msg = f'{kb.mode_str}'
        kb_parent = kb.parent
        while kb_parent is not None:
            msg = f'{kb_parent.mode_str} > ' + msg
            kb_parent = kb_parent.parent
        print(msg, file=sys.stdout)
    elif keyword == 'context':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        
        msg = kb.nice_mode_str()
        kb_parent = kb.parent
        while kb_parent is not None:
            msg = kb_parent.nice_mode_str() + '\n' + msg
            kb_parent = kb_parent.parent
        print(msg, file=sys.stdout)


    # SYNTAX RELATED
    elif keyword == 'syntax':
        if len(args) == 0:
            print(kb.syntax_str_all_levels().strip(), file=sys.stdout)
        else:
            msg = ''
            for arg in args:
                match arg:
                    case [Token(label='STRING'|'SYMBOL', value=s)]:
                        assert isinstance(s, str)
                        info = kb.syntax_str_all_levels(s).strip()
                        if len(info) > 0:
                            msg += info + '\n'
                    case _:
                        msg = create_usage(keyword, [[], ['STRING'], ['SYMBOL']])
                        raise KurtException(f'ParseError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
            msg = '\n'.join(sorted([line for line in msg.split('\n') if len(line) > 0]))
            print(msg, file=sys.stdout)
    elif keyword == 'prefix':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=rbp)]:
                    assert isinstance(op, str)
                    assert isinstance(rbp, int)
                    new_stuff.append((op, rbp))    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'INT']])
                    raise KurtException(f'ParseError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for (op, rbp) in new_stuff:
            kb.add_prefix(op, rbp)
    elif keyword == 'postfix':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=lbp)]:
                    assert isinstance(op, str)
                    assert isinstance(lbp, int)
                    new_stuff.append((op, lbp))    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'INT']])
                    raise KurtException(f'ParseError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for (op, lbp) in new_stuff:
            kb.add_postfix(op, lbp)
    elif keyword == 'infix':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=lbp), Token(label='INT', value=rbp)]:
                    assert isinstance(op, str)
                    assert isinstance(lbp, int)
                    assert isinstance(rbp, int)
                    new_stuff.append((op, lbp, rbp))    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'INT', 'INT']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for (op, lbp, rbp) in new_stuff:
            kb.add_infix(op, lbp, rbp)
    elif keyword == 'arity':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=arity)]:
                    assert isinstance(op, str)
                    assert isinstance(arity, int)
                    new_stuff.append((op, arity))    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'INT']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for (op, arity) in new_stuff:
            kb.add_arity(op, arity)
    elif keyword == 'brackets':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=lbracket), Token(label='STRING'|'SYMBOL', value=rbracket)]:
                    assert isinstance(lbracket, str)
                    assert isinstance(rbracket, str)
                    new_stuff.append((lbracket, rbracket))    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for (lbracket, rbracket) in new_stuff:
            kb.add_brackets(lbracket, rbracket)
    elif keyword == 'bindop':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for op in new_stuff:
            kb.add_bindop(op)
    elif keyword == 'chain':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            assert isinstance(arg, list)
            chain: list[str] = []
            if len(arg) < 1:
                raise KurtException(f'ParseError: chains must contain at least one infix operator')
            for op_token in arg:
                match op_token:
                    case Token(label='STRING'|'SYMBOL', value=op):
                        assert isinstance(op, str)
                        chain.append(op)
                    case _:
                        msg = create_usage(keyword, [[], ['STRING', 'STRING'], ['STRING', 'STRING', 'STRING'], ['STRING', 'STRING', 'STRING', 'STRING']])
                        raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
            kb.check_with_other_chains(chain)  # might raise an exception
            new_stuff.append(chain)    # first collect
        for chain in new_stuff:
            kb.add_chain(chain)

    elif keyword == 'flat':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for op in new_stuff:
            kb.add_flat(op)
    elif keyword == 'sym':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for op in new_stuff:
            kb.add_sym(op)
    elif keyword == 'bool':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        for args_i in args:
            match args_i:
                case []:
                    assert False, f'BUG: empty args in `bool` should have been caught earlier'
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    kb.add_bool(op, [0])
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=a)]:
                    assert isinstance(op, str)
                    assert isinstance(a, int)
                    kb.add_bool(op, [a])
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=a), Token(label='INT', value=b)]:
                    assert isinstance(op, str)
                    assert isinstance(a, int) and isinstance(b, int)
                    kb.add_bool(op, [a, b])
                case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=a), Token(label='INT', value=b), Token(label='INT', value=c)]:
                    assert isinstance(op, str)
                    assert isinstance(a, int) and isinstance(b, int) and isinstance(c, int)
                    kb.add_bool(op, [a, b, c])
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'INT'], ['STRING', 'INT', 'INT'], ['STRING', 'INT', 'INT', 'INT']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'var':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for args_i in args:
            match args_i:
                case []:
                    assert False, f'BUG: empty args in `var` should have been caught earlier'
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for op in new_stuff:
            kb.add_var(op)
            if mainstream:
                log(f'var {op}', f'added variable', kb.level)
    elif keyword == 'const':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for args_i in args:
            match args_i:
                case []:
                    assert False, f'BUG: empty args in `const` should have been caught earlier'
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for op in new_stuff:
            kb.add_const(op)
            if mainstream:
                log(f'const {op}', f'added constant', kb.level)
    elif keyword == 'alias':
        if len(args) == 0:
            print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
        new_stuff = []
        for args_i in args:
            match args_i:
                case []:
                    assert False, f'BUG: empty args in `alias` should have been caught earlier'
                case [Token(label='STRING'|'SYMBOL', value=s), Token(label='STRING'|'SYMBOL', value=t)]:
                    assert isinstance(s, str) and isinstance(t, str)
                    new_stuff.append((s, t))    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING', 'STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        for (s, t) in new_stuff:
            kb.add_alias(s, t)

    # THEORY AND PROOF RELATED
    elif keyword == 'theory':
        if len(args) > 0:
            msg = create_usage(keyword, [[]])
            raise KurtException(f'EvalError: {keyword} does not take any arguments', keyword_token.column)
        print(kb.theory_str(), file=sys.stdout)

    elif keyword == 'implications':
        if len(args) > 0:
            msg = create_usage(keyword, [[]])
            raise KurtException(f'EvalError: {keyword} does not take any arguments', keyword_token.column)
        print(kb.theory_str(op=IMPL_SYMBOL), file=sys.stdout)

    elif keyword == 'use':
        if len(args) == 0:
            print(kb.theory_str(keyword=keyword), file=sys.stdout)
        else:
            formulas = []
            for expr in args:
                try:
                    formulas.append(eval_use(kb, expr, label, filename, line, mainstream, keyword))  # use the expression as an assumption
                except KurtException:
                    # let's forget about the `formulas`
                    raise
            for f in formulas:
                kb.theory_append(f)
                if mainstream:
                    log(f.formula_str(kb), f.reason, kb.level)

    elif keyword == 'def':
        if len(args) == 0:
            print(kb.theory_str(keyword=keyword), file=sys.stdout)
        else:
            formulas = []
            lhs_consts = []
            for expr in args:
                try:
                    f, lc = eval_def(kb, expr, label, filename, line, mainstream)  # use the expression as a definition
                    formulas.append(f)
                    lhs_consts.append(lc)
                except KurtException:
                    # let's forget about the `formulas` and `lhs_consts`
                    raise
            for (f, lc) in zip(formulas, lhs_consts):
                kb.theory_append(f)
                if mainstream:
                    reason = f'{line} defining `{lc}`'
                    log(f'def {expr_str(expr, kb)}', reason, kb.level-1)  # log the new constant

    elif keyword == 'todo':
        # works like a joker!  however, what to store in the theory?  add a todo token
        if len(args) == 0:
            # `todo` inside proofs, a joker for the next statement, even a `qed`
            kb.theory_append(eval_use(kb, todo_token, label, filename, line, mainstream, keyword))  # use the expression as an assumption
            todo = decorate_reason(False, f'todo', filename, str(line))
            kb.todo_add(todo)
        else:
            for expr in args:
                # `todo F`, adds `F` like an axiom and takes a note of the todo
                kb.theory_append(eval_use(kb, expr, label, filename, line, mainstream, keyword))  # use the expression as an assumption
                todo = decorate_reason(False, f'todo {expr_str(expr, kb)}', filename, str(line))
                kb.todo_add(todo)

    elif keyword == 'thus':
        if len(args) == 0:
            raise KurtException(f'EvalError: `{keyword}` takes an expression as argument')
        elif len(args) == 1:
            expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
            kb = eval_thus(kb, expr, label, filename, line, mainstream)  # use the expression as a conclusion
        else:
            raise KurtException(f'ParseError: `show` takes only one formula, no comma-separated list allowed')

    elif keyword == 'break':
        if len(args) > 0:
            raise KurtException(f'EvalError: `{keyword}` does not take any arguments')
        kb = decrease_level(kb)                    # drop current level and perform some checks
        if mainstream:
            log('break', f'{line} forget the last proof or local scope', kb.level)

    elif keyword == 'show':
        if len(args) == 0:
            print(kb.show_str(), file=sys.stdout)
        elif len(args) == 1:
            expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
            kb = eval_show(kb, expr, label, filename, line, mainstream)
        else:
            raise KurtException(f'ParseError: `show` takes only one formula, no comma-separated list allowed')

    elif keyword == 'proof':                  # opens a new block (scope)
        if len(args) > 0:
            raise KurtException(f'EvalError: `{keyword}` takes no arguments')
        kb = eval_proof(kb, mainstream)

    elif keyword == 'qed':            # closes the last block (scope) and checks that the last promised formula has been proved
        if len(args) > 0:
            raise KurtException(f'EvalError: `{keyword}` takes no arguments')
        kb = eval_qed(kb, filename, line, mainstream)

    elif keyword == 'assume':
        if len(args) == 0:
            raise KurtException(f'EvalError: `{keyword}` takes an expression as argument')
        kb = eval_openblock(kb, ('assume', args), line, mainstream=False)  # open a new block
        for expr in args:
            try:
                f = eval_use(kb, expr, label, filename, line, mainstream=False, keyword='use')  # use the expression as an assumption
                kb.theory_append(f, symbol_level_prev=True)
            except KurtException:
                kb = decrease_level(kb)
                raise
        if mainstream:
            reason = f'{line} open local scope with assumption'
            assumptions_str = ', '.join([expr_str(arg, kb) for arg in args])
            log(f'{keyword} {assumptions_str}', reason, kb.level-1)  # log the new constant

    elif keyword == 'fix':
        debug(args)
        msg = 'EvalError: `fix` takes new constants or boolean expressions'
        if len(args) == 0:
            raise KurtException(msg)
        # add the new constants and their constraints (if boolean expressions are given)
        kb = eval_openblock(kb, ('fix', args), line, mainstream=False)  # open a new block
        for expr in args:  # args is a list of expressions
            try:
                kb = eval_fix(kb, expr, filename, line, mainstream)
            except KurtException:
                kb = decrease_level(kb)  # close the block on error
                raise      # the same exception again
        if mainstream:
            reason = f'{line} open local scope with (possibly constrained) new constants'
            args_str = [expr_str(expr, kb) for expr in args]
            log(f'{keyword} {", ".join(args_str)}', reason, kb.level-1)  # log the new constants

    elif keyword == 'pick':
        msg = 'EvalError: `pick` takes a new constant, keyword `with` and a formula , e.g. `pick x with F(x)`'
        if len(args) == 0:
            raise KurtException(msg)
        for expr in args:
            try:
                match expr:
                    case [Token(label='SYMBOL', value=new_const), Token(label='SYMBOL', value='with'), *fact_expr] if isinstance(new_const, str) and not kb.is_const(new_const):
                        kb, fact = eval_pick(kb, expr[0], fact_expr, filename, line, mainstream)
                    case _:
                        raise KurtException(msg)
            except KurtException:
                kb = decrease_level(kb)
                raise
        if mainstream:
            reason = f'{line} open local scope with new constant `{new_const}`'
            log(f'{keyword} {new_const} with {expr_str(fact, kb)}', reason, kb.level-1)  # log the new constants
    else:
        assert False, f'BUG: unknown keyword, got `{keyword}`'

    # finally return the possibly modified knowledgebase
    return kb

def letter_generator() -> Iterator[str]:
    letters = 'abcdefghijklmnopqrstuvwxyz'
    for size in itertools.count(1):
        for combo in itertools.product(letters, repeat=size):
            yield ''.join(combo)

def chop_off_comma(e: Expr) -> list[Expr]:
    match e:
        case [Token(label='SYMBOL', value=v), *tail] if v == COMMA_SYMBOL:
            return tail
        case _:
            return [e]

def split_by_comma(e: Expr) -> list[Expr]:
    if isinstance(e, Token):
        return [e]        # nothing to split
    args = []
    current_arg: list[Expr] = []
    for ei in e:
        match ei:
            case Token(label='SYMBOL', value=v) if v==COMMA_SYMBOL:
                if len(current_arg) == 0:
                    raise KurtException(f'ParseError: nothing to separate with a comma', ei.column)
                args.append(current_arg)
                current_arg = []
            case _:
                current_arg.append(ei)
    if len(current_arg) == 0 and len(args) > 0:
        assert isinstance(e[-1], Token) and e[-1].label=='SYMBOL' and e[-1].value==COMMA_SYMBOL
        raise KurtException(f'ParseError: nothing to separate with a comma', e[-1].column)
    if len(current_arg) > 0:
        args.append(current_arg)
    return args

def eval_expression(keyword_token: Optional[Token], expr_list: list[Expr], label: str, kb: KnowledgeBase, line: int, filename: str, mainstream: bool) -> KnowledgeBase:
    if keyword_token is None:
        # expression without keyword: try to derive the formula and add it to the theory
        if len(expr_list) == 0:
            return kb
        for expr in expr_list:
            if not bool_expr(expr, kb, strict=False):   # not strict, since we are possibly adding new symbols
                raise KurtException(f'EvalError: must evaluate to boolean, got `{expr_str(expr, kb)}`')
            reasons, _ = derive_expr(expr, filename, mainstream, State.empty(), kb)  # this might raise ProofError exceptions
            if len(reasons) == 1:
                reason = decorate_reason(mainstream, reasons[0], filename, str(line))
            else:
                assert len(reasons) > 1
                assert isinstance(expr, list) and len(expr) > 2
                assert len(expr) == len(reasons) + 1
                line_strs: list[str] = []
                for clause, reason, letter in zip(expr[1:], reasons, letter_generator()):
                    line_str = str(line) + letter
                    line_strs.append(line_str)
                    reason = decorate_reason(mainstream, reason, filename, line_str)
                    label = ''
                    sub_f = Formula(kb, clause, line_str, filename, label, reason, keyword='')
                    kb.theory_append(sub_f)                         # add sub to the knowledge base
                    if mainstream:
                        log(sub_f.formula_str(kb), reason, kb.level)
                reason = decorate_reason(mainstream, f'by {", ".join(line_strs)} "and-intro"', filename, str(line))
            label = ''
            f = Formula(kb, expr, str(line), filename, label, reason, keyword='')
            kb.theory_append(f)                         # add it to the knowledge base
            if mainstream:
                log(f.formula_str(kb), reason, kb.level)
        return kb
    else:
        # expression with a keyword
        debug(expr_list)
        kb = eval_keyword_expression(keyword_token, expr_list, label, kb, line, filename, mainstream)
        return kb

########################
## kurt type checking ##
########################

def bool_expr(expr: Expr, kb: KnowledgeBase, strict: bool=True) -> bool:
    # this is the non-deep check
    # - at some places we are strict
    # - at other places (like eval_use) we are not strict, since we are adding a new formula
    match expr:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_bool_var(v):
            return True                    # boolean variables
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and not kb.is_bool_var(v):
            if strict or kb.is_used(v):
                return 0 in kb.bool_sig(v)
            else:
                return True   # not used yet!  so it will soon be boolean
        case Token(label='TODO', value=''):
            return True
        case [Token(label='SYMBOL', value=v), *tail] if v==SUB_SYMBOL:
            return bool_expr(tail[2], kb, strict)
        case [Token(label='SYMBOL', value=v), *_]:
            return bool_expr(expr[0], kb, strict)
    return False

def expr_column(expr : Expr) -> int:
    match expr:
        case Token():
            assert isinstance(expr.column, int)
            return expr.column
        case [*children]:
            assert len(children) > 0
            return expr_column(children[0])

def type_check_expression(expr: Expr, kb: KnowledgeBase) -> None:
    # this uses the declared boolean-ness of some symbols via `kb.bool` and `bool_expr`
    # and in contrast to `bool_expr` it goes done the expression tree
    match expr:

        # substitutions
        case [Token(label='SYMBOL', value=v), var_x, a, A] if v==SUB_SYMBOL:
            if not is_var_token(var_x, kb):
                raise KurtException(f'TypeError: first arg of `sub` must be variable symbol (a boolean var is not allowed)')
            if bool_expr(a, kb):
                raise KurtException(f'TypeError: second arg of `sub` must be a non-boolean expression')
            type_check_expression(A, kb)

        # most expressions: prefix, postfix, infix, bindop, ...
        case [Token(label='SYMBOL', value=op), *tail]:
            assert isinstance(op, str)
            # (1) do the args fit the declared type in `bool_sig`
            for idx in range(1, len(expr)):
                if idx in kb.bool_sig(op) and not bool_expr(expr[idx], kb, strict=False):
                    raise KurtException(f'TypeError: arg number {idx} of `{op}`, i.e., `{expr_str(expr[idx], kb)}` must be boolean', column=expr_column(expr[idx]))
            # (2) additional checks for binding operators
            if kb.is_bindop(op):
                # check that the first argument is either a variable or a boolean expression
                match tail[0]:
                    case Token(label='SYMBOL', value=v):
                        if not isinstance(v, str):
                            raise KurtException(f'TypeError: first arg of binding operator must be boolean expression or symbol, got {v}', column=expr_column(tail[0]))
                        if kb.is_const(v):
                            raise KurtException(f'TypeError: first arg of binding operator must not be constant, got a constant `{v}`', column=expr_column(tail[0]))
                        pass         # ok!
                    case [*cond]:
                        if not bool_expr(cond, kb):
                            raise KurtException(f'TypeError: first arg of binding operator must be variable or boolean, got {cond}')
                        # check existence of a free variable
                        fv: set[str] = free_bound_vars(cond, kb)[0]
                        if len(fv) == 0:
                            raise KurtException(f'TypeError: first arg must be or must contain at least one free variable')
                    case _:
                        assert False, f'BUG: did not match {tail[0]} while type checking'
            # (3) recursively go deep and check
            for e in tail:
                type_check_expression(e, kb)

#################
## kurt prover ##
#################
# the strategy:
# - list of rules with LHS and RHS
# - check for an expr whether it matches the RHS (is the match unique)?  can we get the list of all matches?  use yield!
# - using the match, instantiate the LHS and look for formulas in the theory until all formulas in the LHS are matched
# - possibly there are hints to quickly find the matching formulas of the LHS
# - record for the current expression the successful rule and the used formulas in the theory
# - if we fail, raise a meaningful exception
#
# an inference rule with LHS {A,B,C} and RHS D
#   A
#   B
#   C
#   ---
#   D
# or written as a kurt formula
#   A and B and C implies D

def log(s: str, reason: str, level: int) -> None:
        indent: str = ' ' * (proof_indent * level)
        if len(reason) == 0:
            print(indent+s, file=sys.stdout)
        else:
            print(f'{(indent+s):<{reason_indent}}; {reason}', file=sys.stdout)

# how to derive a formula?
# - equalities lead to two rules
#    e.g. `a = b` and `sub x a F` leads to `sub x b F`
# - logical inference rules
#    e.g. 
#        F and (F implies G)
#    thus
#        G
# some rules are built-in, some are in kurt code
# however, basically all rules follow the scheme:
#        A and B and C implies D
# steps:
# 1. check whether the formula to prove matches D
# 2. search for A and B and C in the theory (with substitution applied)

# "forall-intro" without condition
#
#       fix ε           ; or use `let` or `take`
#         bla bla
#         F(ε)
#       thus ∀ε F(ε)    ; forall-intro
# ensure that the current level contains only ε as a new symbol and nothing else (also no assumptions)

def forall_intro(expr: Expr, kb: KnowledgeBase, filename: str, mainstream: bool) -> str:

    # step 0: ensure we are one level up
    if kb.level == 0:
        raise KurtException(f'EvalError: forall-intro requires one level up')
    assert kb.parent is not None
    kb_parent: KnowledgeBase = kb.parent
    fv = free_vars_only(expr, kb_parent) | free_bool_vars_only(expr, kb_parent)  # collect all free variables in the expression to prove

    # step 1: dissect the forall quantified expression
    # - check the bounded variables and collect conditions
    # - chop-off the quantifiers
    fix_expr = kb.mode_expr
    assert isinstance(fix_expr, list)    # must be true, since `fix` takes a list of expressions
    body = expr  # this is the loop variable, where we will chop off the forall quantifiers
    for i in range(len(fix_expr)):
        match body:
            case [Token(label='SYMBOL', value=op), bound_v_expr, inner_body] if op == FORALL_SYMBOL:
                # forall quantifier found
                if not equal_expr(bound_v_expr, fix_expr[i]):
                    raise KurtException(f'EvalError: the bound variable in the forall quantifier must match the expression of the `fix` statement, got `{expr_str(bound_v_expr, kb)}` instead of `{expr_str(fix_expr[i], kb)}`')
                body = inner_body  # continue with the body of the forall, this is the loop increment
            case _:
                # no forall quantifier found, possibly we have a matching free variable
                fix_expr_i = fix_expr[i]
                if is_var_token(fix_expr_i, kb_parent) or is_bool_var_token(fix_expr_i, kb_parent):
                    assert isinstance(fix_expr_i, Token) and isinstance(fix_expr_i.value, str)
                    if fix_expr_i.value not in fv:
                        raise KurtException(f'EvalError: the fixed variable `{fix_expr_i.value}` must occur free in the expression to prove, got `{expr_str(expr, kb)}`')
                else:
                    raise KurtException(f'EvalError: the fixed expression must be a variable symbol, got `{expr_str(fix_expr_i, kb)}`')

    # step 2: the remaining body must have been derived
    if len(kb.theory) == 0:
        raise KurtException(f'Nothing was proved in the last local scope')
    reasons, _ = derive_expr(body, filename, mainstream, State.empty(), kb)
    reason  = ' '.join(reasons) if len(reasons) > 0 else ''  # join all reasons
    reason += f', then by "forall-intro"'
    return reason

def exists_elim(expr: Expr, kb: KnowledgeBase, filename: str, mainstream: bool) -> str:
    # finally `exists_elim`
    # (1) check there are no assumptions
    unproven_exprs = [f.expr for f in kb.theory if not f.is_proven()]
    if len(unproven_exprs) > 0:   # (i)
        raise KurtException(f'ProofError: there are assumptions on the current level, `thus` can thus only conclude an implication or an universal quantified formula to close the block, got `{expr_str(unproven_exprs[-1], kb)}`')
    # (2) derive the expression
    reasons, _ = derive_expr(expr, filename, mainstream, State.empty(), kb)
    reason  = ' '.join(reasons) if len(reasons) > 0 else ''  # join all reasons
    reason += f', then by "exist-elim"'
    return reason

def not_intro(expr: Expr, kb: KnowledgeBase) -> str:

    # step 0: ensure we are one level up
    if kb.level == 0:
        raise KurtException(f'EvalError: neg-intro requires one level up')
    assert kb.parent is not None

    # step 1: dissect the `not` expression
    assert isinstance(expr, list)      # must be true, since `expr` is a not-expression
    body = expr[1]

    # step 2: check that `body` was assumed
    assumptions = [f.expr for f in kb.theory if not f.is_proven()]  # collect all assumptions on the current level
    if len(assumptions) == 1:              # assumptions is one formula
        assumptions = assumptions[0]
    else:                                  # assumptions is a conjunction
        # some assumptions might be conjunctions as well, so flattening might help
        assumptions = flatten_all([Token(label='SYMBOL', value=AND_SYMBOL)] + assumptions, kb)   # flatten
    if not equal_expr(assumptions, body):
        raise KurtException(f'EvalError: {expr_str(body, kb)} does not match any assumption on the current level')

    # step 3: `false` must have been derived
    msg = f'ProofError: the contradiction (aka `false`) was not proved'
    if len(kb.theory) == 0:
        raise KurtException(msg)
    last_expr = kb.theory[-1].expr
    match last_expr:
        case Token(label='SYMBOL', value=FALSE_SYMBOL):
            pass
        case _:
            raise KurtException(msg)
    return f'by "not-intro" (derived from last local scope)'

# this function is called in one case of `eval_thus`
def impl_intro(expr: Expr, kb: KnowledgeBase) -> str:
    
    # step 1: collect all assumptions of the current level
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: nothing was shown in the (sub-)proof')
    last_formula = kb.theory[-1]
    premise = [f.expr for f in kb.theory if not f.is_proven()]
    if not last_formula.is_proven():
        raise KurtException(f'ProofError: last formula in a (sub-)proof must be derived and can not be assumed with `use`')
    conclusion = last_formula.expr        # last element is the conclusion

    # step 2: form a formula using the last formula in the current level
    if len(premise) == 0:                  # just the conclusion (empty premise)
        result = conclusion
        reason = f'by last local scope'
    else:
        if len(premise) == 1:              # premise is one formula
            premise = premise[0]
        else:                              # premise is a conjunction
            premise = flatten_all([Token(label='SYMBOL', value=AND_SYMBOL)] + premise, kb)   # bring to normalform
        result = [Token(label='SYMBOL', value=IMPL_SYMBOL), premise, conclusion]       # construct implication
        reason = f'by "impl-intro" (derived from last local scope)'

    # step 3: compare against the planned expression `expr`
    if equal_expr(expr, result):
        if kb.verbose:
            print(f'goal    {expr_str(expr, kb)}',   file=sys.stdout)
            print(f'derived {expr_str(result, kb)}', file=sys.stdout)
        return reason
    else:
        raise KurtException(f'ProofError: could not prove    {expr_str(expr, kb)}\n            instead got        {expr_str(result, kb)}')

def apply_subst(expr: Expr, s: State, kb: KnowledgeBase) -> Expr:
    """
    Deeply apply `subst` to `expr`, capture-avoiding:
    - Uses `walk` to head-normalize at each node.
    - Extends `blocked` with the binder's bound variable when descending.
    - Does not mutate `subst` (no delete/copy tricks).
    """
    expr = s.walk(expr)  # head-normalize first

    match expr:
        # atom after head-normalization
        case Token():
            return expr

        # binding operator: recurse into body with extended blocked
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bound_v), *tail] if isinstance(op, str) and kb.is_bindop(op):
            assert isinstance(bound_v, str)
            body = expr[2:]
            new_body = [apply_subst(c, s.block_always(bound_v), kb) for c in body]
            return [expr[0], expr[1], *new_body]
        
        # general case: recurse into all children
        case [*exprs]:
            return [apply_subst(c, s, kb) for c in exprs]
        
        # never reach this one!
        case _:
            assert False, f'BUG: did not match expression `{expr_str(expr, kb)}` in `apply_subst`'

def bool_vars(expr: Expr, kb: KnowledgeBase) -> set[str]:
    # return a set of the boolean variables in expression `e`
    match expr:

        # the token of a boolean
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_bool_var(v):
            return set([v])
        
        # any other token is not a boolean variable
        case Token():
            return set()
        
        # collect the boolean variables in the children, covers also `e==[]`
        case [*children]:
            bv: set[str] = set()
            for child in children:
                bv.update(bool_vars(child, kb))
            return bv
        
    assert False, f'BUG: did not match expression `{expr_str(expr, kb)}` in `bool_vars`'

# note that a variable can be free and bound at the same time in an expression
# note that here are only considering non-boolean variables
def free_bound_vars(expr: Expr, kb: KnowledgeBase) -> tuple[set[str], set[str]]:
    # return two lists sets of the free and bound variables in expression `e`
    match expr:

        # the token of a variable is (for now) a free variable (until it is bound higher up in the AST)
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
            return set([v]), set()
        
        # any other token doesn't have free or bound variables
        case Token():
            return set(), set()
        
        # binding operators "bind" free variables
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bound_v), *tail] if isinstance(op, str) and kb.is_bindop(op):
            fv, bv = free_bound_vars(tail, kb)
            if bound_v in fv:           # `bound_v` appears freely in `tail`
                fv.remove(bound_v)      # remove from the free vars, since in `expr` it is bound
            assert isinstance(bound_v, str)
            bv.add(bound_v)             # add to the bound vars (also if it wasn't a free variable, i.e., didn't appear in `tail`)
            return fv, bv
        
        # collect the free and bound variables in the children, covers also `e==[]`
        case [*children]:
            fv: set[str] = set()
            bv: set[str] = set()
            for child in children:
                fv0, bv0 = free_bound_vars(child, kb)
                fv.update(fv0)
                bv.update(bv0)
            return fv, bv
        
    assert False, f'BUG: did not match expression `{expr_str(expr, kb)}` in `free_bound_vars`'

# new variable names just for internal use
def new_var_name() -> str:
    if not hasattr(new_var_name, "counter"):
        new_var_name.counter = 0            # static variable of the function
    new_var_name.counter += 1               # get a new number
    return f'$$var{new_var_name.counter}'   # the `$$` ensures that it is not a kurt variable that the user can define

# new boolean variable names just for internal use
def new_bool_var_name() -> str:
    if not hasattr(new_bool_var_name, "counter"):
        new_bool_var_name.counter = 0             # static variable of the function
    new_bool_var_name.counter += 1                # get a new number
    return f'%%bool{new_bool_var_name.counter}'   # the `%%` ensures that it is not a kurt variable that the user can define

def remove_outer_forall_quantifiers(expr: Expr, kb: KnowledgeBase) -> Expr:
    expr = deepcopy_expr(expr)  # deep copy to avoid modifying the original expression

    # chop off all outer universal quantifiers and rename their bound vars
    while is_forall(expr):          
        assert isinstance(expr, list) and len(expr) == 3
        assert isinstance(expr[1], Token) and isinstance(expr[1].value, str)
        bound_var = expr[1].value
        free_var = new_var_name()
        s = State({bound_var: Token(label='SYMBOL', value=free_var)}, frozenset(), frozenset())
        expr = apply_subst(expr[2], s, kb)
    return expr

# ALL variables are renamed on the formula level
# * rename free vars in `expr` with generated names to avoid clashes with other expressions
#   this is necessary, because free variables are implicitly universally bound per formula,
#   i.e., their meaning should be shared inside a formula (or while matching also between formulas)
# * renaming bound variables:
#   we should never rename bound variables (here `$x`) only locally, since they might appear in free variables (here `%A`), example:
#      forall $x %A  implies  sub $x $a %A      "forall-elim"
#   if we rename `$x` on the LHS of the implication we get:
#      forall $z %A  implies  sub $x $a %A      "forall-elim"
#   which doesn't work, since in `%A` there is not a `$z` at the correct position
# * however, renaming bound variables globally (for the whole formula) is fine, since it enables requirement (1) in `generate_all_combinations`
#   so the renaming of bound variables makes also "exists-elim" possible
# * since symbols become `bound` on the fly, we have to maintain a set of bound variables that get globally replaced
def rename_all_vars(expr: Expr, kb: KnowledgeBase) -> Expr:
    expr = deepcopy_expr(expr)  # deep copy to avoid modifying the original expression

    # rename all variables (yes, some are renamed again, this can be improved later (TODO))
    expr = rename_all_vars_rec(expr, kb)[0]
    return expr

def rename_all_vars_rec(expr: Expr, kb: KnowledgeBase, s: Optional[State] = None, bound_vars: set[str]|None = None) -> tuple[Expr, State]:
    # initialize the bound_vars if not given (don't put `set()` as the default value into the signature, since it is only called once and then modified, THIS LEADS TO A VERY SUBTLE BUG)
    if bound_vars is None:
        bound_vars = set()
    if s is None:
        s = State.empty()

    # state `s` contains the replacements so far, which are applied also down the AST
    match expr:

        # a token of an (at least) locally free (boolean or not) variable will be replaced either by a known substitution or with a new name
        case Token(label='SYMBOL', value=var) if isinstance(var, str) and not kb.is_const(var) and (kb.is_var(var) or kb.is_bool_var(var) or var in bound_vars):
            new_expr = s.lookup(var)
            if new_expr is None:
                if kb.is_var(var) or var in bound_vars:
                    # note that `bound_vars` do not have to be declared as variables in `kb`, since from the binding operator it is clear that they are variables
                    new_var = new_var_name()
                else:
                    new_var = new_bool_var_name()
                new_expr = Token(label='SYMBOL', value=new_var, column=expr.column, origin=expr.origin)
            return new_expr, s.bind(var, new_expr)  # extend the state with the new binding

        # any other token is not modified
        case Token():
            return expr, s

        # binding operator expression
        case [Token(label='SYMBOL', value=bind_op),
              Token(label='SYMBOL', value=bind_var), *body] \
              if isinstance(bind_op, str) and kb.is_bindop(bind_op) and isinstance(bind_var, str):

            # operator gets processed with current scope (actually nothing to do)
            head1, s = rename_all_vars_rec(expr[0], kb, s, bound_vars)

            # `bind_var` and `body` are processed in the context, that `bind_var in bound_vars`
            new_bound_vars = bound_vars | {bind_var}
            head2, s = rename_all_vars_rec(expr[1], kb, s, new_bound_vars)

            # `body` gets new scope including the bound variable
            new_body = []
            for child in body:
                new_child, s = rename_all_vars_rec(child, kb, s, new_bound_vars)
                new_body.append(new_child)

            return [head1, head2, *new_body], s

        # all other expressions
        case [*children] if children:
            new_children = []
            for child in children:
                new_child, s = rename_all_vars_rec(child, kb, s, bound_vars)
                new_children.append(new_child)
            return new_children, s

    assert False, f'BUG: did not match expression `{expr_str(expr, kb)}` in `rename_all_vars`'

def is_sub(expr):
    return isinstance(expr, list) and len(expr)==4 and isinstance(expr[0], Token) and expr[0].label=='SYMBOL' and expr[0].value=='sub'

# check that `expr_a` does not contain freely any variables that are bound at the locations of `token_x` in `expr_A`
# that's quite complicated, so instead we check whether they are among the bound variables of `expr_A`
def bound_var_safe(expr: Expr, token_x: Token, expr_a: Optional[Expr], expr_A: Expr, kb: KnowledgeBase) -> bool:
    if expr_a is None:
        return True
    else:
        [free_a, _] = free_bound_vars(expr_a, kb)      # ignore `bound_a`
        [_, bound_A] = free_bound_vars(expr_A, kb)     # ignore `free_A`
        return free_a.isdisjoint(bound_A)


def generate_all_combinations(expr: Expr, token_x: Token, expr_a: Optional[Expr], kb: KnowledgeBase) -> Iterator[tuple[Optional[Expr], Expr]]:
    # generate all `($a, %A)` such that `expr == sub $x $a %A`
    # however, two requirements:
    # (1) `$x` does not appear in `expr` as a free or bound variable, this is ensured by renaming bound variables in `expr`
    # (2) `$a` does not contain freely any variables that are bound in `%A` (actually only bound at the locations of `$x`)
    [free, bound] = free_bound_vars(expr, kb)
    var_x = token_x.value
    assert var_x not in free and var_x not in bound, f'BUG: `{var_x}` must not appear in `{expr_str(expr, kb)}`'

    ### allow only one subterm to be replaced, much more efficient
    for (cand_expr_a, cand_expr_A) in all_single_hole_decompositions(expr, token_x):
        if expr_a is None  or  equal_expr(expr_a, cand_expr_a):
            if bound_var_safe(expr, token_x, cand_expr_a, cand_expr_A, kb):     # requirement (2)
                yield (cand_expr_a, cand_expr_A)

def all_single_hole_decompositions(expr: Expr, token_x: Token) -> Iterator[tuple[Expr, Expr]]:
    # For each node in expr, yield (node_value, expr_with_that_node_replaced_by_token_x).
    def extract_at_path(e: Expr, path: list[int]) -> tuple[Expr, Expr]:
        """Extract subterm at path and return (subterm, expr_with_hole)"""
        subterm = get_at_path(e, path)
        expr_with_hole = replace_at_path(e, path, token_x)
        return (subterm, expr_with_hole)
    
    # Generate all paths in the expression tree
    for path, _ in iter_nodes(expr):
        subterm, expr_with_hole = extract_at_path(expr, path)
        yield (subterm, expr_with_hole)

def get_at_path(expr: Expr, path: list[int]) -> Expr:
    """Get the subexpression at the given path."""
    if len(path) == 0:
        return expr
    i = path[0]
    assert isinstance(expr, list) and i < len(expr)
    return get_at_path(expr[i], path[1:])


def replace_at_path(expr: Expr, path: list[int], token_x: Token) -> Expr:
    """Return a deep copy of expr where the subexpression at `path` is replaced by `token`."""
    if len(path) == 0:
        return token_x
    i = path[0]
    new_list = deepcopy_expr(expr)
    assert isinstance(new_list, list)
    new_list[i] = replace_at_path(new_list[i], path[1:], token_x)
    return new_list

def iter_nodes(expr: Expr, path_prefix: list[int]|None = None) -> Iterator[tuple[list[int], Expr]]:
    """Yield (path, subexpression) for every node (including the root)."""
    if path_prefix is None:
        path_prefix = []
    yield path_prefix, expr
    if isinstance(expr, list):
        for i, child in enumerate(expr):
            yield from iter_nodes(child, path_prefix + [i])

def generate_one_combination(expr: Expr, var_x: str, expr_a, expr_A, kb) -> Iterator[tuple[Optional[Expr], Expr]]:
    # no blocked vars, since we are at the top level
    s = State({var_x: expr_a}, frozenset(), frozenset())   # substitute `$x` with `expr_a`
    cand_expr = apply_subst(expr_A, s, kb)
    if equal_expr(cand_expr, expr):
        # we have a match, i.e., `expr = sub $x $a $A` where `$a` is `expr_a` and `$A` is `expr_A`
        yield expr_a, expr_A

# couple of problems:
# - also we are generating some wrong combinations where we replace bound variables in `%A` with `$x`, what is allowed, can `$a` contain any bound variables of `%A`?  probably not!
def match_against_sub(expr: Expr, pattern: Expr, tail: list[tuple[Expr, Expr]], s: State, kb: KnowledgeBase) -> Iterator[State]:

    # check that `expr` is not a sub expression
    assert not is_sub(expr)

    # some checks for the pattern which must be `sub $x a A`
    assert isinstance(pattern, list) and len(pattern) == 4
    token_sub, token_x, p_a, p_A = pattern
    assert isinstance(token_sub, Token) and token_sub.value == SUB_SYMBOL
    assert isinstance(token_x, Token) and isinstance(token_x.value, str)
    ## assert kb.is_var(token_x.value)   # we don't require bound variables to be declared variable already
    var_x = token_x.value

    # `sub $x  a  A` or
    # `sub $x $a  A` or
    # `sub $x  a %A` or
    # `sub $x $a %A`
    var_a:  Optional[str]
    a:      Optional[Expr]
    if isinstance(p_a, Token) and isinstance(p_a.value, str) and kb.is_var(p_a.value):
        var_a = p_a.value
        a = s.lookup(var_a)    # `$a` might have been assigned earlier, will be None otherwise
        #  `a` is none, we can choose it later
    else:
        var_a = None
        a = p_a                                       # `a` is fixed

    all_combinations: Iterator[tuple[Optional[Expr], Expr]]  # generator of `a` and `A` that create a match
    var_A: Optional[str]
    if isinstance(p_A, Token) and isinstance(p_A.value, str) and kb.is_bool_var(p_A.value):
        var_A = p_A.value
        A = s.lookup(var_A)    # `%A` might have been assigned earlier, will be None otherwise
        if A is None:
            all_combinations = generate_all_combinations(expr, token_x, a, kb)
        else:
            all_combinations = generate_one_combination(expr, var_x, a, A, kb)    # `%A` was already assigned earlier
    else:
        var_A = None
        # TODO: in this case we should do something more sophisticated, since we could have
        #       arity F 1
        #       bool F 0 1
        #       sub $x $a F %A
        # where we should be creative with `%A` as well, i.e., we should go on with matching, but keeping in mind we can use `sub $x`
        # i.e., go on with matching against:  `F sub $x $a %A`
        # what about
        #       arity G 2
        #       bool G 0 1 2
        #       sub $x $a G %A %B
        # that should be a problem, however, `generate_all_combinations` must be a bit more sophisticated
        all_combinations = generate_one_combination(expr, var_x, a, p_A, kb)

    for (expr_a, expr_A) in all_combinations:
        # check whether `expr_A` is boolean
        if bool_expr(expr_A, kb):
            s_local = s     # keeps `s` available in the next iteration
            # we don't have to match `expr` against `expr_A` since `all_combinations` and also `one_combinations` ensure that they match
            if var_A is not None and s.lookup(var_A) is None:
                s_local = s_local.bind(var_A, expr_A)   # extend the state with the new binding for `%A`
            if var_a is not None and expr_a is not None:
                s_local = s_local.bind(var_a, expr_a)   # extend the state with the new binding for `$a`
            # now that we found a substitution for `$a` and `%A`
            #debug(f'$a=`{expr_str(expr_a, kb) if expr_a is not None else "?"}`  %A=`{expr_str(expr_A, kb)}`', kb)
            yield from unify_exprs_with_patterns(tail, s_local, kb)

# helper functions
T = TypeVar('T')
def split_into_lists(lst: list[T], n: int) -> Iterator[list[list[T]]]:
    """
    Lazily yield every way to split `lst` into `n` consecutive, non-empty sub-lists.

    Example
    -------
    >>> list(split_into_lists([1, 2, 3, 4], 2))
    [[[1], [2, 3, 4]],
     [[1, 2], [3, 4]],
     [[1, 2, 3], [4]]]
    """
    if n == 1:                     # one block left → whole tail
        yield [lst]
        return
    if len(lst) < n:               # impossible: not enough items
        return
    # choose a cut-point for the first block, then recurse
    for i in range(1, len(lst) - n + 2):        # ensure room for `n-1` more blocks
        head = lst[:i]
        tail = lst[i:]
        for rest in split_into_lists(tail, n - 1):
            yield [head] + rest

def partitions(seq:list[T], k: int) -> Iterator[list[list[T]]]:
    """
    Yield each way to split `seq` into `k` non-empty subsets.

    Partitions themselves are unordered, and the elements
    inside each block keep the order they had in `seq`.
    """
    n = len(seq)
    assert 1 <= k <= n, 'BUG: need 1 ≤ k ≤ len(seq)'

    # ---- base cases -------------------------------------------------------
    if k == 1:             # everything in one block
        yield [seq]
        return
    if k == n:             # every element stands alone
        yield [[x] for x in seq]
        return

    # ---- recursive step ---------------------------------------------------
    first, *rest = seq

    # (1) `first` gets its *own* new block
    for part in partitions(rest, k - 1):
        yield [[first]] + part

    # (2) `first` joins each existing block
    for part in partitions(rest, k):
        for i in range(len(part)):
            # copy so the recursive call’s list isn’t mutated
            new_part = [block[:] for block in part]
            new_part[i].append(first)
            yield new_part

def is_var_token(e:Expr, kb) -> bool:
    if not (isinstance(e, Token) and e.label == 'SYMBOL'):
        return False
    assert isinstance(e.value, str)
    return kb.is_var(e.value)

def is_bool_var_token(e:Expr, kb) -> bool:
    if not (isinstance(e, Token) and e.label == 'SYMBOL'):
        return False
    assert isinstance(e.value, str)
    return kb.is_bool_var(e.value)

def rename_bound_var(e: Expr, old_v: str, new_v: str) -> Expr:
    match e:
        case Token(label='SYMBOL', value=v) if v == old_v:
            return Token('SYMBOL', value=new_v)
        case [*children]:
            return [rename_bound_var(c, old_v, new_v) for c in children]
        case _:
            return e

# the non-recursive calls are having a single expr and a single pattern, the recursive calls then might have more
# each "case" with a recursive call loops over all generated local substitutions
# `exprs_patterns`:   [(e1, p1), (e2, p2), ...] = zip([e1, e2, ...], [p1, p2, ...])
# this list is necessary for the `[*_]` case, i.e., for matching two lists
# `two_sided` means that variables in the exprs can also be assigned
def unify_exprs_with_patterns(exprs_patterns: list[tuple[Expr, Expr]], s: State, kb: KnowledgeBase) -> Iterator[State]:
    if len(exprs_patterns) == 0:
        yield s     # we emptied the matching tasks and found a substitution
    else:
        [(expr, pattern), *tail] = exprs_patterns   # unpack

        # lazy style: apply `walk` before processing, i.e., apply the substitution
        # (alternative: eager style: apply `walk` to the tail after each change to the substitution)
        expr = s.walk(expr)
        pattern = s.walk(pattern)

        if equal_expr(expr, pattern):
            # equal, just continue with the `tail`
            yield from unify_exprs_with_patterns(tail, s, kb)

        elif is_var_token(pattern, kb) or is_var_token(expr, kb) or is_bool_var_token(expr, kb) or is_bool_var_token(pattern, kb):
            if is_var_token(pattern, kb):
                # `pattern` is a variable
                assert isinstance(pattern, Token) and isinstance(pattern.value, str)
                v = pattern.value
                assert s.lookup(v) is None
                if not s.occurs(v, expr) and not s.is_blocked_as_domain(v) and not s.contains_blocked_as_range(expr):
                    # we can safely assign `v` without creating infinite substitutions
                    s = s.bind(v, expr)   # extend the substitution
                    #debug(f'assigning: {v} to {expr_str(expr, kb)}')
                    yield from unify_exprs_with_patterns(tail, s, kb)

            if is_var_token(expr, kb):
                # `expr` is a variable (the case where `expr` and `pattern` are both variables is handled by the previous case)
                assert isinstance(expr, Token) and isinstance(expr.value, str)
                u = expr.value
                assert s.lookup(u) is None
                if not s.occurs(u, pattern) and not s.is_blocked_as_domain(u) and not s.contains_blocked_as_range(pattern):
                    # we can safely assign `u` without creating infinite substitutions
                    s = s.bind(u, pattern)   # extend the substitution
                    #debug(f'assigning: {u} to {expr_str(pattern, kb)}')
                    yield from unify_exprs_with_patterns(tail, s, kb)

            if is_bool_var_token(pattern, kb):
                # `pattern` is a boolean variable
                assert isinstance(pattern, Token) and isinstance(pattern.value, str)
                V = pattern.value
                assert s.lookup(V) is None
                if not s.occurs(V, expr) and not s.is_blocked_as_domain(V):
                    # we can safely assign `V` without creating infinite substitutions
                    s = s.bind(V, expr)   # extend the substitution
                    yield from unify_exprs_with_patterns(tail, s, kb)

            if is_bool_var_token(expr, kb):
                # `expr` is a boolean variable
                assert isinstance(expr, Token) and isinstance(expr.value, str)
                W = expr.value
                assert s.lookup(W) is None
                if not s.occurs(W, pattern) and not s.is_blocked_as_domain(W):
                    # we can safely assign `W` without creating infinite substitutions
                    s = s.bind(W, pattern)   # extend the substitution
                    yield from unify_exprs_with_patterns(tail, s, kb)

        else:
            # branch on `pattern` for unification
            match pattern:

                # binding operator matching (rename bound variable before!)
                case [Token(label='SYMBOL', value=op_p), Token(label='SYMBOL', value=v_p), *args_p] if isinstance(op_p, str) and kb.is_bindop(op_p):
                    if op_p == SUB_SYMBOL and not is_sub(expr):   
                            # asymmetric:  don't match a `sub` expr to a `sub` pattern (an infinite loop!)
                            yield from match_against_sub(expr, pattern, tail, s, kb)
                    # in any case: additionally binding ops match against their matching binding ops
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), Token(label='SYMBOL', value=v_e), *args_e]:
                            if op_p==op_e and len(args_p)==len(args_e):
                                assert isinstance(v_p, str) and isinstance(v_e, str)
                                # Rename the expr-side binder body from v_e to v_p (alpha-eq) before unifying.
                                args_e = [deepcopy_expr(args_e_i) for args_e_i in args_e]
                                args_e = alpha_rename_binder_body(args_e, v_e, v_p, kb)
                                # Block the pattern binder (domain+range) during descent
                                s_local = s.block_always(v_p)
                                yield from unify_exprs_with_patterns(list(zip(args_e, args_p)) + tail, s_local, kb)

                # list matching for flat and non-symmetric operators (do allow different lengths)
                case [Token(label='SYMBOL', value=op_p), *tail_p] if isinstance(op_p, str) and (kb.is_flat(op_p) and not kb.is_sym(op_p)):
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), *tail_e] if isinstance(op_e, str) and op_e==op_p:
                            if len(tail_e) >= len(tail_p):  # we can assign variables in `tail_p` to elements of `tail_e`
                                splits = split_into_lists(tail_e, len(tail_p))
                                for split in splits:
                                    # convert singletons into elements and add the operator to longer lists
                                    split_expr: list[Expr] = [child[0] if len(child)==1 else [expr[0], *child] for child in split]
                                    yield from unify_exprs_with_patterns(list(zip(split_expr, tail_p)) + tail, s, kb)
                            else:
                                splits = split_into_lists(tail_p, len(tail_e))
                                for split in splits:
                                    # convert singletons into elements and add the operator to longer lists
                                    split_pattern: list[Expr] = [child[0] if len(child)==1 else [pattern[0], *child] for child in split]
                                    yield from unify_exprs_with_patterns(list(zip(tail_e, split_pattern)) + tail, s, kb)

                # list matching for non-flat and symmetric operators (do not allow different lengths)
                case [Token(label='SYMBOL', value=op_p), *tail_p] if isinstance(op_p, str) and (not kb.is_flat(op_p) and kb.is_sym(op_p)):
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), *tail_e] if isinstance(op_e, str) and op_e == op_p and len(tail_e) == len(tail_p):
                            # For symmetric operators, try all permutations of one side
                            for perm_tail_e in itertools.permutations(tail_e):
                                yield from unify_exprs_with_patterns(list(zip(perm_tail_e, tail_p)) + tail, s, kb)

                # list matching for flat and symmetric operators (do allow different length)
                case [Token(label='SYMBOL', value=op_p), *tail_p] if isinstance(op_p, str) and (kb.is_flat(op_p) and kb.is_sym(op_p)):
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), *tail_e] if isinstance(op_e, str) and op_e==op_p:
                            if len(tail_e) >= len(tail_p):  # we can assign variables in `tail_p` to elements of `tail_e`
                                subsets = partitions(tail_e, len(tail_p))  # get `len(tail_p)` many subsets of `tail_e`
                                for subset in subsets:
                                    # get all permutations of the subsets
                                    perms = itertools.permutations(subset)
                                    for perm in perms:
                                        # convert singletons into elements and add the operator to longer lists
                                        perm_expr: list[Expr] = [child[0] if len(child)==1 else [expr[0], *child] for child in perm]
                                        yield from unify_exprs_with_patterns(list(zip(perm_expr, tail_p)) + tail, s, kb)
                            else:
                                subsets = partitions(tail_p, len(tail_e))  # get `len(tail_e)` many subsets of `tail_p`
                                for subset in subsets:
                                    # get all permutations of the subsets
                                    perms = itertools.permutations(subset)
                                    for perm in perms:
                                        # convert singletons into elements and add the operator to longer lists
                                        perm_pattern: list[Expr] = [child[0] if len(child)==1 else [pattern[0], *child] for child in perm]
                                        yield from unify_exprs_with_patterns(list(zip(tail_e, perm_pattern)) + tail, s, kb)

                # list matching (same length, no special operators)
                case [*_] if isinstance(expr, list) and len(expr)==len(pattern):
                    yield from unify_exprs_with_patterns(list(zip(expr, pattern)) + tail, s, kb)

                case _:
                    # we didn't match the pattern, so we cannot extend the substitution
                    pass

        
def expr_without_boolean_var(expr: Expr, kb: KnowledgeBase) -> bool:
    # check whether `expr` is a final expression, i.e., it does not contain any boolean variables
    match expr:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_bool_var(v):
            return False  # boolean variable
        case Token():
            return True   # not a boolean variable
        case [*children]:
            return all(expr_without_boolean_var(child, kb) for child in children)

def free_vars_only(e: Expr, kb: KnowledgeBase) -> set[str]:
    return free_bound_vars(e, kb)[0]

def free_bool_vars_only(e: Expr, kb: KnowledgeBase) -> set[str]:
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_bool_var(v):
            return {v}
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
            return set()
        case Token():
            return set()
        case [*children]:
            fv: set[str] = set()
            for child in children:
                fv.update(free_bool_vars_only(child, kb))
            return fv
    assert False, f'BUG: did not match expression `{expr_str(e, kb)}` in `free_bool_vars_only`'

def alpha_rename_binder_body(body: list[Expr], old: str, new: str, kb: KnowledgeBase) -> list[Expr]:
    # rename bound occurrences of `old` to `new` *inside this binder body only*.
    # stop if we encounter an inner binder that also binds `old`.
    def ren(e: Expr) -> Expr:
        match e:
            case Token(label='SYMBOL', value=s) if isinstance(s, str) and s == old:
                # This occurrence is bound by the current binder thus rename
                return Token(label='SYMBOL', value=new)
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bv), *tail] \
                 if isinstance(op, str) and kb.is_bindop(op) and isinstance(bv, str):
                if bv == old:
                    # A new binder that *rebinds* `old` thus do not rename under it
                    return [Token(label='SYMBOL', value=op),
                            Token(label='SYMBOL', value=bv), *tail]
                # Otherwise, keep renaming under this binder
                return [Token(label='SYMBOL', value=op),
                        Token(label='SYMBOL', value=bv),
                        *[ren(c) for c in tail]]
            case [*children]:
                return [ren(c) for c in children]
            case _:
                return e
    return [ren(c) for c in body]

def fresh_like(name: str, avoid: set[str], kb: KnowledgeBase) -> str:
    # make a fresh variable name of the same sort as `name` not in `avoid`.
    # uses your generators; ensure kb treats them as variables.
    if kb.is_bool_var(name):
        while True:
            cand = new_bool_var_name()
            if cand not in avoid: return cand
    else:
        while True:
            cand = new_var_name()
            if cand not in avoid: return cand

def capture_avoiding_replace(A: Expr, x: str, t: Expr, s: State, kb: KnowledgeBase) -> Expr:
    # compute A[x := t] with α-renaming to avoid capture.
    # strategy:
    #  1) if a binder in A binds `bv` where bv ∈ FV(t), α-rename that binder locally to a fresh name.
    #  2) then perform the actual replacement using apply_subst({x: t}) with `blocked` handling.
    FVt = free_vars_only(t, kb)

    def go(e: Expr, blk: frozenset[str]) -> Expr:
        # do NOT use apply_subst here (we are restructuring A itself).
        match e:
            case Token():
                return e

            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bv), *body] if isinstance(op, str) and kb.is_bindop(op) and isinstance(bv, str):
                # if this binder binds x, x is not free below thus no substitution under it,
                # but we still recurse structurally to catch nested binders that might need α-renaming
                if bv == x:
                    new_body = [go(c, blk | {bv}) for c in body]
                    return [Token(label='SYMBOL', value=op),
                            Token(label='SYMBOL', value=bv), *new_body]

                # if bv occurs free in t, α-rename this binder locally
                if bv in FVt:
                    # Build an avoid set to keep name fresh w.r.t. t and current e
                    avoid = FVt | free_vars_only([Token(label='SYMBOL', value=op),
                                                  Token(label='SYMBOL', value=bv), *body], kb) \
                            | {x} | set(blk)
                    bv2 = fresh_like(bv, avoid, kb)
                    body_ren = alpha_rename_binder_body(body, bv, bv2, kb)
                    new_body = [go(c, blk | {bv2}) for c in body_ren]
                    return [Token(label='SYMBOL', value=op),
                            Token(label='SYMBOL', value=bv2), *new_body]

                # Normal descent: no α-renaming needed
                new_body = [go(c, blk | {bv}) for c in body]
                return [Token(label='SYMBOL', value=op),
                        Token(label='SYMBOL', value=bv), *new_body]

            case [*children]:
                return [go(c, blk) for c in children]

        return e

    # 1) α-rename binders in A that would capture free vars of t
    A_alpha = go(A, s.blocked_as_domain)

    # 2) now do the capture-avoiding replacement using your apply_subst
    #    (blocked prevents touching bound occurrences of x)
    return apply_subst(A_alpha, s.bind(x, t), kb)

# trigger a single substitution in `expr` if possible, return the new expression and the new state
def trigger_sub(expr: Expr, s: State, kb: KnowledgeBase) -> tuple[Expr, State]:
    expr = deepcopy_expr(expr)
    # fully apply current substitution (capture-avoiding via blocked)
    expr = apply_subst(expr, s, kb)

    def trigger_sub_core(e: Expr, s: State) -> tuple[Expr, State]:
        e = s.walk(e)  # head-normalize again

        match e:
            # sub: [sub, $x, t, A] (must be the first case)
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), t, A] if isinstance(op, str) and op == SUB_SYMBOL:
                assert isinstance(x, str)
                s_local = s
                # normalize the pieces
                t_s, s_local = trigger_sub_core(t, s_local)
                # block x while normalizing A (x is a binder for A)
                A_s, s_local = trigger_sub_core(A, s_local.block_always(x))

                # only fire when the schema is concrete (no %A style bool vars)
                if not contains_bool_vars(A_s, kb):
                    # we're done with the binder x; unblock it BEFORE returning
                    s_after = s_local.unblock(x)
                    # perform capture-avoiding A[x:=t]
                    A_repl = capture_avoiding_replace(A_s, x, t_s, s_after, kb)
                    return A_repl, s_after
                else:
                    # do NOT leave x permanently blocked if we don't fire
                    s_after = s_local.unblock(x)
                    return [e[0], e[1], t_s, A_s], s_after

            # binding operator: [op, bv, *body]
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bv), *body] if isinstance(op, str) and kb.is_bindop(op) and isinstance(bv, str):
                # enter binder scope
                s_scope = s.block_always(bv)
                new_body = []
                for c in body:
                    c_local, s_scope = trigger_sub_core(c, s_scope)
                    new_body.append(c_local)
                # leave binder scope (pop the block)
                s_after = s_scope.unblock(bv)
                return [e[0], e[1], *new_body], s_after

            # any other list
            case [*children] if len(children) > 0:
                result = []
                s_local = s
                for c in children:
                    c_local, s_local = trigger_sub_core(c, s_local)
                    result.append(c_local)
                return result, s_local

            # any other token
            case _:
                return e, s

    return trigger_sub_core(expr, s)

# unify a list of expression with the theory
def match_all_theory(exprs: list[Expr], s: State, kb: KnowledgeBase) -> tuple[bool, list[Formula], State]:
    match exprs:

        # we unified all `exprs`, done!
        case []:
            return True, [], s
        
        # still at least one to go
        case [expr, *tail]:
            # iterate over all formulas of the theory
            blocked = frozenset()   # no blocked variables
            for candidate in kb.all_theory():
                # iterate over all possible substitutions that unify
                # basically, this is two-sided matching, aka unification

                for s_cand in unify_exprs_with_patterns([(candidate.simplified_expr, expr)], s, kb):
                    # try to unify the rest of the expressions (the `tail`)
                    s_local = s_cand
                    tail_local = []
                    for e in tail:
                        e_local, s_tail = trigger_sub(e, s_local, kb)
                        tail_local.append(e_local)
                    success, found_formulas, s_final = match_all_theory(tail_local, s_local, kb)
                    if success:
                        return True, [candidate, *found_formulas], s_final   # match was found!  BINGO!
            # no match so far, however, possibly `expr` is a conjunction that we can split into pieces
            match expr:
                # e.g., (A and B) implies C, then `expr = ['and', A, B]`
                case [Token(label='SYMBOL', value=v), *exprs] if v == AND_SYMBOL:
                    # the only place where we might call `match_all_theory` with a list longer than one
                    assert len(exprs) > 0
                    return match_all_theory(exprs + tail, s, kb)  # try to match the arguments of the conjunction
            # still no match, so we return `None` and an empty list
            return False, [], State.empty()  # could not find a match among the candidate `patterns`

    # we calling `match_all_theory` wrongly, bug!
    assert False, f'BUG: `match_all_theory` did not cover all cases for {exprs}'

# what is happening:
# 0. deep copy `proven_formula` and rename all its variables (happens already in the construction of it)
# 1. split `proven_formula` into `conclusion` and `premises`
# 2. ensure that there are no universal quantifiers around the whole formula (see `remove_forall`)
# 3. match `expr` against `conclusion` (and create a substitution that replaces free variables in conclusion)
#    free vars in `expr` must be matched against `free variables in `conclusion`
#    free vars in `conclusion` can be matched against anything in `expr`
# 4. match `premises` against the theory (but allow substitutions in both directions)
#    free vars in `premises` 
def impl_elim(expr: Expr, proven_formula: Formula, filename: str, mainstream: bool, s: State, kb: KnowledgeBase) -> tuple[str, State]:

    # continue with the renamed and simplified variant of `proven_formula` that is generated during the construction of it
    formula_expr: Expr = proven_formula.simplified_expr

    # assign `conclusion` and `premises`
    premise: Optional[Expr] = None
    if is_implication(formula_expr):      # case 1: implication with a premise
        assert isinstance(formula_expr, list)
        premise    = remove_outer_forall_quantifiers(formula_expr[1], kb)
        conclusion = remove_outer_forall_quantifiers(formula_expr[2], kb)
    elif is_iff(formula_expr):
        assert isinstance(formula_expr, list)
        op_token = formula_expr[0]
        assert isinstance(op_token, Token)
        LHS = remove_outer_forall_quantifiers(formula_expr[1], kb)
        RHS = remove_outer_forall_quantifiers(formula_expr[2], kb)
        LHSimpliesRHS = proven_formula.clone([op_token.clone(IMPL_SYMBOL), LHS, RHS], kb)
        reason, s_local = impl_elim(expr, LHSimpliesRHS, filename, mainstream, s, kb)
        if len(reason) > 0:
            return reason, s_local
        RHSimpliesLHS = proven_formula.clone([op_token.clone(IMPL_SYMBOL), RHS, LHS], kb)
        reason, s_local = impl_elim(expr, RHSimpliesLHS, filename, mainstream, s, kb)
        if len(reason) > 0:
            return reason, s_local
        return '', State.empty()    # no luck this time
    else:                                 # case 2: "implication" with an empty premise (think of `true implies $A`)
        conclusion = formula_expr

    # to unify `conclusion` and `premise` iterate over all possible substitutions of the `conclusion`
    # however, we must not change bound variables, so we block the free variables of `expr` since they are universally quantified
    blocked_as_domain = frozenset(s.blocked_as_domain | free_bound_vars(expr, kb)[0])
    s = State(s.subst, blocked_as_domain, s.blocked_as_range)
    #debug(f'NEW: try to show {expr_str(expr, kb)} from {formula_ref(proven_formula, filename, mainstream)} which is {expr_str(formula_expr, kb)}')
    #debug(f'match {expr_str(expr, kb)} against {expr_str(conclusion, kb)}')
    s_final: Optional[State] = State.empty()
    for s_matched in unify_exprs_with_patterns([(expr, conclusion)], s, kb):
        if premise is None:
            s_final = s_matched
            #debug(f'BINGO! {expr_str(conclusion, kb)} implies {expr_str(expr, kb)}')
            #debug(f'       with {s_final}')
            break           # bingo!  we found one
        else:
            # deep copy of `premise` is necessary, since `match_all_theory` will be called several times with the different substitution `subst`
            # and we have to apply the various substitutions to it, which might change from call to call
            premise_local, s_local = trigger_sub(premise, s_matched, kb)

            # search for the premise as well, i.e., match the theory against the `premise`
            #debug(f'match {expr_str(premise_local, kb)} against the theory')
            #debug(f'matched_subst: {s_matched}')
            success, matched_formulas, s_final = match_all_theory([premise_local], s_local, kb)
            if success:
                #debug(f'BINGO! {expr_str(premise_local, kb)} follows from {[expr_str(f.simplified_expr, kb) for f in matched_formulas]}')
                #debug(f'       with {s_final}')
                break           # bingo!  we found one
    else:
        if is_implication(formula_expr):
            # maybe we shouldn't split it into premise and conclusion
            premise = None
            s_final = _first_or_none(unify_exprs_with_patterns([(expr, formula_expr)], s, kb))
            if s_final is None:
                #debug(f'failed: could not show {expr_str(formula_expr, kb)} implies {expr_str(expr, kb)}')
                return '', State.empty()    # no luck this time
        else:
            #debug(f'failed: could not show {expr_str(conclusion, kb)} implies {expr_str(expr, kb)}')
            return '', State.empty()     # no luck this time

    # create meaningful `reason`
    if kb.verbose:
        log('', f'  expression to prove: {expr_str(expr, kb)}', kb.level)
        log('', f'  formula used: {expr_str(proven_formula.expr, kb)}', kb.level)
    reason: str = f'by '
    if premise is not None:
        refs = ', '.join([formula_ref(ref, filename, mainstream) for ref in matched_formulas])
        if len(matched_formulas) > 1:
            reason += f'({refs}), '
        else:
            reason += f'{refs}, '
    reason += f'{formula_ref(proven_formula, filename, mainstream)}'
    return reason, s_final    # bingo!  found an implication (and a substitution)

def derive_expr(expr: Expr, filename: str, mainstream: bool, s: State, kb: KnowledgeBase) -> tuple[list[str], State]:

    # do we have a joker?
    if len(kb.theory) > 0:
        match kb.theory[0].expr:
            case Token(label='TODO', value=''):
                return ['by a miracle (todo)'], s

    # rename variables
    expr = remove_outer_forall_quantifiers(expr, kb)
    expr = rename_all_vars(expr, kb)    # rename variables

    # "top-intro"
    if isinstance(expr, Token) and expr.label=='SYMBOL' and expr.value==TRUE_SYMBOL:
        return ['by "top-intro"'], s

    # "impl-elim": iterate over the previously proven formulas that form the current theory.
    # this part also handles restatements (as implication without a premise)
    for proven_formula in kb.all_theory():
        reason, s_matched = impl_elim(expr, proven_formula, filename, mainstream, s, kb)
        if len(reason) > 0:
            return [reason], s_matched

    # if `expr` is a conjunction we can try to derive each of the subexpressions
    # make sure that, if it was a conjunction, then the (growing) substitution should apply to all clauses!
    match expr:
        case [Token(label='SYMBOL', value=v), *clauses] if v==AND_SYMBOL:
            reasons: list[str] = []
            assert len(clauses) > 0
            for clause in clauses:
                more_reasons, s = derive_expr(clause, filename, mainstream, s, kb)  # this might raise an exception
                reasons.extend(more_reasons)
            return reasons, s

    # couldn't derive formula using any of the rules
    raise KurtException(f'ProofError: can not derive expression')

LHS_token = Token('SYMBOL', value='$$LHS$$') # a special token to mark the LHS of the last row

def scan_parse_check_eval(input_line: str, kb: KnowledgeBase, line: int, filename: str, mainstream:bool=False) -> KnowledgeBase:

    # we store the LHS of the initial line that starts a chain and the infix operators seen so far
    if not hasattr(scan_parse_check_eval, "_initial_LHS"):     # use static variable of the function
        scan_parse_check_eval._initial_LHS = None              # LHS of the line starting the chain
    if not hasattr(scan_parse_check_eval, "_chained_ops"):     # use static variable of the function
        scan_parse_check_eval._chained_ops = []                # infix operators of the chain seen so far

    # read the static variables
    lhs: Optional[Expr] = scan_parse_check_eval._initial_LHS
    ops: list[str] = scan_parse_check_eval._chained_ops

    # scan the input line and prepare for the parsing
    ts = PeekableGenerator(scan_string(input_line, kb))    # runs the lexer

    # chain management before parsing
    debug(f'chain management before parsing: {lhs=}, {ops=}, {input_line=}')
    chained = False
    first_token: Optional[Token] = ts.peek # do we have a chainable operator at the start?
    if first_token is not None:
        first_label = first_token.label
        first_value = first_token.value
        if first_label == 'SYMBOL' and isinstance(first_value, str):
            if first_value not in keywords and kb.is_chainable(first_value):
                if lhs is not None and ops != []:       # did we start a chain before?
                    ops.append(first_value)   # add to the chain so far
                    resulting_op: Optional[str] = kb.get_chain_op(ops)
                    if resulting_op is not None:
                        chained = True
                        ts.prepend(LHS_token)             # add dummy token to the front
                        debug(f'continuing chain with {first_value=}, resulting in {resulting_op=}')
                    else:
                        raise KurtException(f'ParseError: invalid chain of operators `{ops}` at line {line} in {filename}')

    # the usual parsing (raises exception if `chained=False` but `first_token` is chainable)
    keyword_token, expr_list, label = parse_tokenstream(ts, kb)  # runs the parser

    # chain management continued
    if chained:
        # case 1: continue chain
        assert isinstance(expr_list, list)
        if len(expr_list) != 1:
            raise KurtException(f'ParseError: expected exactly continued chain, not several comma-separated ones')
        assert isinstance(expr_list[0], list)
        assert len(expr_list[0]) == 3 and expr_list[0][1] == LHS_token, f'ParseError: expected exactly continued chain, not {expr_list}'
        assert resulting_op is not None    # otherwise we wouldn't be in `chained` mode
        expr_list[0][0] = Token('SYMBOL', resulting_op)   # replace the infix operator
        assert lhs is not None
        expr_list[0][1] = deepcopy_expr(lhs)      # replace the dummy token
    else:
        if len(expr_list) == 1 and kb.starts_a_chain(expr_list[0]):
            # case 2: start new chain
            assert isinstance(expr_list[0], list)
            assert len(expr_list[0]) == 3
            e0, e1, _ = expr_list[0]
            assert isinstance(e0, Token) and isinstance(e0.value, str)
            lhs = e1           # store the LHS (which is after parsing the second token)
            ops = [e0.value]   # store the initial operator (which is after parsing the first token)
        else:
            # case 3: reset the chain
            lhs = None
            ops = []

    # evaluate
    kb   = eval_expression(keyword_token, expr_list, label, kb, line, filename, mainstream) # evaluation

    # write back the static variables
    scan_parse_check_eval._initial_LHS = lhs
    scan_parse_check_eval._chained_ops = ops
    return kb

def load_file(filename: str, kb: KnowledgeBase, markdown: bool=False, path: list[str]=theory_path, mainstream:bool=False) -> KnowledgeBase:
    # files are always loaded into level
    level = kb.level       # save current level
    if not filename.endswith('.kurt'):
        filename += '.kurt'
    try:    # just for handling OS errors
        fname = find_file(filename, path)    # search along the path
        if len(fname) == 0:
            raise OSError
        load_level = kb.get_load_level(fname)
        if load_level is not None:
            raise KurtException(f'EvalError: can not load library `{fname}` twice, it has already been loaded on level {load_level}')
        with open(fname, encoding='utf-8') as f:
            kb = read_eval_loop(f, kb, markdown, mainstream=mainstream)
    except OSError as e:
        # we have to add `from None` to avoid exception chaining, since we only want to see the KurtException
        raise KurtException(f'EvalError: unable to open `{filename}` searching at {path}') from None
    
    # checks after closing the file
    if kb.level != level:
        kb.level = level       # set levels back before raising the exception
        raise KurtException(f'\nEvalError: inside `{fname}` not all blocks closed, missing "qed"?')
    if len(kb.show) != 0:
        s = '\nNot shown:\n'
        for f in kb.show:
            s += f'    {f.formula_str(kb):<{reason_indent-4}}; {os.path.basename(f.filename)}:{f.line}'
        raise KurtException(f'{s}\n\nEvalError: inside `{fname}` not all promised formulas were proven.')
    kb.libs.append(fname)
    return kb

###########################
## commandline interface ##
###########################

def prompt(level: int, line: int, continued: bool=False) -> str:
    s = '>' * level
    if continued:
        s += f'.[{line}] '                        # line continuation
    else:
        s += f'![{line}] '                        # the bangs mean "show!"
    return s

def read_eval_loop(input_stream: TextIO, kb: KnowledgeBase, markdown: bool=False, mainstream: bool=False) -> KnowledgeBase:
    is_file   = (input_stream.name != '<stdin>')   # for non files we have a fancy prompt and we don't stop if an KurtException comes
    line       = 1
    continued  = False
    input_line = ''
    if not is_file and readline:
        readline.parse_and_bind("tab: complete")    # enable tab completion
    while True:
        try:
            if not is_file:
                prompt_text = prompt(kb.level, line, continued)
                new_line = input(prompt_text).rstrip()     # uses readline
                new_line = replace_latex_syntax(new_line)  # automatic replacements in the shell before running the scanner
            else:
                new_line = input_stream.readline()
                if not new_line:
                    break
                new_line = new_line.rstrip()
            new_line = new_line.expandtabs(tab_indent)     # tabs are ok, but are converted
            if markdown:
                if new_line.startswith(' ' * md_indent):
                    new_line = new_line[md_indent:]  # ignore the first `md_indent` spaces
                else:
                    continue                              # ignore the line
            input_line += new_line
            try:
                kb = scan_parse_check_eval(input_line, kb, line, input_stream.name, mainstream)
            except StopIteration:
                input_line += ' '  # add a space to the input line
                continued = True
                line += 1
                continue
            except KurtException as e:
                if e.column is None:
                    e.column = proof_indent * kb.level      # put the marker `^` at the beginning of the expression
                if e.filename is None:
                    e.filename = input_stream.name
                    e.line     = line
                    if e.filename == '<stdin>':
                        msg = f'\n'
                    else:
                        msg = f'\nFile `{e.filename}`, line {e.line}:\n'
                    msg += f'{input_line}\n'
                    msg += f'{" " * e.column + "^"}\n'
                    e.msg = msg + e.msg
                if is_file:
                    raise e    # reraise the error, since we were called by `load_file`
                else:
                    print(e.msg, file=sys.stderr)  # show the error and go on
            input_line = ''  # Reset input
            continued = False
            line += 1
        except EOFError:
            print("\nBye!", file=sys.stdout)      # this only happens when Ctrl-d is pressed in the interactive session
            break
    return kb

def find_file(fname: str, path: list[str]) -> str:
    for p in path:
        cand = os.path.join(p, fname)
        if os.path.isfile(cand):
            return cand
    return ''   # empty string

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=f'a simple proof assistant ({made_by})')
    parser.add_argument("filename", nargs='?',                       help=f'check the proof in the file, w/o filename start interactively')
    parser.add_argument('-i', '--interactive',  action='store_true', help=f'enter read-eval-print loop after loading `filename`')
    parser.add_argument('-m', '--markdown',     action='store_true', help=f'run on `.md` files instead of `.kurt`, will ignore everything that is not indented by {md_indent} spaces')
    parser.add_argument('-r', '--reason-indent', type=int, default=reason_indent, help=f'specify the indentation for reasons (default: {reason_indent})')
    parser.add_argument('-p', '--path',                              help=f'specify the path where `load` looks for theories after checking {theory_path}')
    parser.add_argument('-v', '--verbose',      action='store_true', help=f'show extra information during proof checking')
    parser.add_argument('-d', '--debug',        action='store_true', help=f'show debugging information')
    parser.add_argument('-t', '--test',         action='store_true', help=f'run unit tests and exit')
    return parser.parse_args()

def run_tests() -> None:
    import os
    import unittest

    # Ensure we are running discovery in the right directory
    test_dir = os.path.join(os.path.dirname(__file__), 'tests')
    loader = unittest.TestLoader()
    suite = loader.discover(start_dir=test_dir, pattern='test_*.py')

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    print(f'\nSUMMARY')
    print(f'Ran {result.testsRun} tests')
    print(f'Failures: {len(result.failures)}')
    print(f'Errors:   {len(result.errors)}')
    print('Status:   ' + ('passed' if result.wasSuccessful() else 'failed'))

def main() -> None:
    print(f'This is Kurt, v{version} ({made_by})', file=sys.stdout)
    args = parse_args()

    # run tests?
    if args.test:
        print('Running tests...', file=sys.stdout)
        run_tests()
        exit(0)

    # debug flag?
    global debug_flag
    debug_flag = args.debug

    # set reason indentation
    global reason_indent
    reason_indent = args.reason_indent

    # readline history
    if readline:
        readline_history_file = os.path.expanduser('~/.kurt_history')         # should work on all platforms
        if os.path.exists(readline_history_file):
            readline.read_history_file(readline_history_file)                 # restore history
        atexit.register(readline.write_history_file, readline_history_file)   # register for automatic saving

    # the knowledge base we start with on level 0
    kb = initial_kb

    # verbosity?
    kb.verbose = args.verbose

    # theory path
    if args.path is not None:
        theory_path[1] = args.path   # overwrite the default 'theory'

    if kb.verbose:
        print(f'Using theory path: {theory_path}', file=sys.stdout)

    try:
        # by default load `default_theory` or nothing
        theory_filename = find_file(default_theory, theory_path)
        if len(theory_filename) > 0:
            kb: KnowledgeBase = load_file(theory_filename, kb, mainstream=False)

        # if there is a filename run the file
        if args.filename is not None:
            mainstream = not args.interactive
            assert kb.level == 0
            kb = load_file(args.filename, kb, mainstream=mainstream)
            assert kb.level == 0
            if mainstream:
                todos = kb.todos()
                n_todos = len(todos)
                if n_todos == 0:
                    log(f'Proof checked.', '', kb.level)
                elif n_todos == 1:
                    log(f'Proof almost checked: {n_todos} todo.', '', kb.level)
                else:
                    log(f'Proof almost checked: {n_todos} todos.', '', kb.level)
                for todo in todos:
                    log(f'  {todo}', '', kb.level)
        else:
            args.interactive = True

    except KurtException as e:
        print(e.msg, file=sys.stderr)

    # read-eval-print loop with exception handling
    if args.interactive:
        kb = read_eval_loop(sys.stdin, kb, mainstream=True)
    exit(0)

if __name__ == '__main__':
    main()
