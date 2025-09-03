#!/usr/bin/env python3
from __future__ import annotations

## kurt.py
# kurt - a programming language for proof writing and checking
# (c) 2025 Stefan Harmeling
# licensed under the MIT License

## for profiling run:
# python -m cProfile -o kurt.prof kurt.py
# python -m cProfile -s time kurt.py proofs/linear-algebra/group.kurt

## processing a kurt-file does the following steps in a single pass
# level1: lexing
# level2: parsing
# level3: simple type checking
# level4: proving

## link to a good explanation of the natural deduction system
# https://leanprover-community.github.io/logic_and_proof/natural_deduction_for_first_order_logic.html

### NEXT
# TODO group.kurt

### TOPICS before releasing 1.0
# TODO when `bool` is called check that the symbol is not yet used
# TODO do calculations with integers and reals
# TODO what should go into `minimal.kurt`?  what into `propositional.kurt` and `first-order.kurt`?
# TODO when calling 'bool a', check that 'a' hasn't been used already (e.g. right after a 'fix a')
# TODO define what get's exported when loading a file, make variables declarations local?
# TODO get coverage of 100% in the unit tests
# TODO test the conditions for forall and exist rules
# TODO get group.kurt working with constants and with `var x, y, z`
# TODO 'thus' with one step shorter, for `qed` we use match`, for `thus` we use equal (otherwise matching the correct variables is difficult)
# TODO allow implicit universal quantification, i.e., all variables $x are automatically universally quantified
# TODO allow implicit universal quantification for boolean variables
# TODO what should be loaded by default?  `minimal.kurt` or `standards.kurt`?
# TODO check all KurtExceptions for ProofError, ParseError, SyntaxError, EvalError
# TODO check the inference for quantifiers, whether there must be more restrictions, or does the renaming handle it?  try to violate them
# TODO implement chains
# TODO `kurt proofs/debug/chains.kurt`: why is the proof ok?  next, turn chain into inequalities, `chain` must be a list of chains
# TODO have `x<y<=z` as a short cut for `x<y and y<=z`, or even store them separately, and also multi-line equations
# TODO local and export features, files should open a new level, but can export statements as axioms ('use') to the level above them
# TODO do multi-line equations and iff, (no indentation necessary, just must be part of a chain, and previous line must be a chain)
# TODO write documentation/tutorial for the language
# TODO refactoring: work through all 'mainstream', can we avoid them?  check also `decorate_reason` and `formula_ref`.  yes, store the reason in the formula, then generate a log string later up, but we don't need the `mainstream` flag anymore, possibly we need it since some impl-elim are also generating logs, similarly, remove the 'filenames' that are passed around
# TODO search all TODO in the code and check whether they are still relevant
# TODO proof like "excluded-middle" are right now for constant `p`, but actually we would like to prove it for all `p`, i.e., `show $p or not $p`, then it can also be used for subsequent proofs, this requires a let statement or the like together with `forall-intro`

### TOPICS before releasing 2.0
# TODO should substitutions be always boolean (see `type_check_expression`)
# TODO variables and syntax should be file only, i.e., the `theory` is exported, but the syntax is not.  problem: how to show formulas that are imported (just as quotes?  e.g. `[equality.kurt] %a and %b implies %b and %a`
# TODO add column information for the exceptions, use `expr_column`
# TODO instead of brute-force matching, use more clever matching, e.g., search for the sub terms, or have a dictionary of all subterms
# TODO let it run locally in the browser, e.g., using Pyodide <https://pyodide.org/en/stable/>, see https://chatgpt.com/share/68387cb6-7df4-8008-af44-da04c4449f10
# TODO namespaces, e.g., for scalar-product.kurt, see `kurt-notes.md`, search for `namespace`

### TOPICS for the future
# TODO let's hardcode the quantifier rules, also the `let`, `take` and `thus` stuff
# TODO macros: `macro ($A // $x=$a) (sub $x $a $A)` expands during parsing
# TODO run profiling
# TODO can we make 'proof by contradiction', one step shorter?  `assume A; contradiction; thus not A`
# TODO what is the difference between `arity f 1` and `prefix f 1`?  
# TODO other ideas for speedup: 
# #    1. Add memoization or caching to deepcopy_expr() if there are repeated shared subtrees.
#      2. Use a tree fingerprint or identity system to detect when actual cloning is needed.
# TODO `find sub $x $a forall $z $A`, does this one work?  where the formula for the substitution is nested
# TODO put lots of negative proof examples in to `tests/proofs` as well
# TODO allow boolean expressions for the bound variable for some variable binding operators
# TODO allow commandline args for setting builtin keywords, such as `implies` and `and` and `=` and `sub`
# TODO CHECK THE IMPLEMENTATION WHETHER CONSTRAINTS (i) and (ii) for bindop are enforced
# TODO check whether we need a version of `equal_expr` that allows bounded renaming
# TODO check number of possible variable names, use letters to be safe
# TODO `def ($A // $x=$a) = sub $x $a $A` as a macro mechanism, i.e., just syntactically instead of `use`
# TODO type checking for `sub $x $a $A` with free and bound variable check
# TODO have `origin` (see class Token) also on the Formula level
# TODO substitutions are only allowed in `use` lines, not in regular stuff, so they are designed to formulate axiom schemata.
# TODO check that `minimal.kurt` is really hard-coded here
# TODO matching set of formulas: first match the ones without substitutions, then the ones with (can we detect, when it doesn't work?)
# TODO create an initial version and start working on the branch
# TODO maybe it is a good idea to always have variables with $x and constants without them.  However, using `$+` might be cumbersome.  So having the ability to write `var (+)` might be useful.
# TODO runtime; currently: `derive_expr` is O(n^k) where n is the length of the theory and k is the maximum number of premises of an proved implication, 
#      this could be speed up with better data structure to store the formulas of the theory, but let's first keep it slow, but understandable
# TODO allow outer forall block around implications
# TODO write kurt integration for vscode, highlight the lines that are proven, https://microsoft.github.io/language-server-protocol/
# TODO two algorithms: constraint based (https://www.youtube.com/watch?v=H7x4THVU4BQ) and substitution based (W)
# TODO redo something like https://terrytao.wordpress.com/2023/12/05/a-slightly-longer-lean-4-proof-tour/
#                          https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/
# TODO organize the implications as a dictionary of lists with the top-level operator of RHS as the key
# TODO implement 'nonassoc', this could then be checked in 'post_process'
# TODO integration:    `int x in (0, 1)  f(x)
# TODO replace `functool.cmp_to_key` and rewrite `compare_expr`
# TODO LBYL and EAFP Coding Style? <https://realpython.com/python-lbyl-vs-eafp/>
# TODO https://en.wikibooks.org/wiki/Haskell/Indentation#:~:text=The%20golden%20rule%20of%20indentation&text=When%20you%20start%20the%20expression,acceptable%20and%20may%20be%20clearer).&text=This%20tends%20to%20trip%20up,expressions%20must%20be%20exactly%20aligned.
# TODO format "latex", also allow custom latex formats
# TODO keep the code below 1000 lines of code!  unlikely...
# TODO use the Token.column information
# TODO create test code for each possible KurtException
# TODO add syntactic sugar for case distinctions

## all external libraries (let's keep the dependencies minimal)
import sys
from unittest import case          # sys.stdin, sys.stderr
if sys.version_info < (3, 10):
    print("Python 3.10 or newer is required, since we are using Python's `match`!  Sorry about that!", file=sys.stderr)
    exit(0)
import os           # os.path.[isfile, dirname, abspath, join, basename, split, expanduser, exists]
import argparse     # argparse.ArgumentParser
import re           # re.[compile, sub, VERBOSE, MULTILINE]
import functools    # functools.cmp_to_key
import atexit       # atexit.register
import inspect      # inspect.stack

import itertools    # itertools.[product, count, chain, permutations]
from dataclasses import dataclass
from typing import TypeAlias, Literal, Callable, TypeVar, Generic, Iterator, TextIO, assert_never

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
    def __init__(self, msg:str, column:int|None=None, line:int|None=None, filename:str|None=None) -> None:
        self.msg:      str      = msg
        self.column:   int|None = column
        self.line:     int|None = line
        self.filename: str|None = filename

## the syntax is stored in a hierarchical knowledge base called `KnowledgeBase`
format_options: list[Format] = ['sexpr', 'normal']         # sexpr: (+ 1 (* 3 4)), normal: (1 + (3 * 4))
keywords: dict[str, str] = {
    'help':        'print this help',
    'parse':       'parse a string and print its representation',
    'tokenize':    'tokenize a string and print its tokens',
    'format':      'choose print representation, i.e. one of "sexpr", "normal"',
    'level':       'current level of the knowledge base',
    'load':        'load file, e.g. load "standards.kurt"',

    'syntax':      'print the current syntax',
    'prefix':      'add prefix operator with right binding power',
    'infix':       'add infix operator with left/right binding powers',
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
    'find':        'print all formulas that match a pattern',
    'implications':'print all implications',

    # formulas
    'use':         'use a formula without proof as a axiom',
    'def':         'define new constant symbol using an equation or equivalence',

    'show':        'plan to prove a formula',
    'proof':       'start a proof block to prove the last planned formula',
    'qed':         'end a proof block, to finish the proof of the last planned formula',

    # opening blocks
    'assume':      'open a block and assume a formula, the block must be finished with `thus`, made for `impl-intro`',
    'fix':         'fix a new constant, possibly as an assumption, the block must be finished with `thus`, made for `forall-intro`',
    'pick':        'picks a new constant `with` assumption, made for `exists-elim`',

    # closing blocks
    'thus':        'finish a block that was started with `assume`, `fix` or `pick`, and prove the given formula using the previous block',
    'break':       'break the current proof block without proving anything, should only be used in the shell'
    }
helper_keywords = ['with']     # for keyword `pick`, e.g., `pick y with F(y)`

keywords_with_parsing = ['use', 'assume', 'def', 'fix'] + ['show', 'thus']

# types
Label:  TypeAlias = Literal['SYMBOL', 'INT', 'FLOAT', 'STRING', 'END']
Value:  TypeAlias = str | int | float
Format: TypeAlias = Literal['sexpr', 'normal']

@dataclass
class Token:
    label: Label
    value: Value
    column: int | None = None
    origin: Value | None = None

    def __repr__(self) -> str:
        return f'{self.value}'
    
    def __lt__(self, other: Token) -> bool:
        return str(self.value) < str(other.value)   # note: this is not a good ordering on integers

def clone_token(expr: Token, new_value: Value|None=None) -> Token:
    return Token(
        label  = expr.label,
        value  = expr.value if new_value is None else new_value,
        column = expr.column,
        origin = expr.origin
    )

class Formula:
    next_id: int = 0
    def __init__(self, kb: KnowledgeBase, expr:Expr, line:str, filename:str, label:str, reason:str, proven:bool):
        self.expr: Expr            = expr               # expression of the formula
        self.simplified_expr: Expr = rename_all_vars(simplify(expr, kb), {}, kb)[0]
        self.line: str             = line               # line of this formula, string since we also want '16a', etc
        self.filename: str         = filename           # file of this formula
        self.label: str            = label              # basically, a name of the formula, e.g., "impl-intro"
        self.reason: str           = reason             # the reason for this formula, e.g., "axiom", "assumption", "def", "by"
        self.proven: bool          = proven             # proven yes or no (for `use` and `assume` and `show`)
        self.id: int               = Formula.next_id    # a unique id for every formula
        Formula.next_id += 1

    def clone(self, kb):
        cloned_f = Formula(
            kb,
            expr     = self.expr,
            line     = self.line,
            filename = self.filename,
            label    = self.label,
            reason   = self.reason,
            proven   = self.proven
        )
        cloned_f.id = self.id
        return cloned_f

    def prefix_str(self) -> str:
        if self.proven:
            return ''
        else:
            return 'use' + ' '     # not yet proven, so like an axiom, introduced via `use` or `assume`
    
    def label_str(self) -> str:
        return f' "{self.label}"'
    
    def __str__(self) -> str:
        return f'{self.prefix_str()}{self.expr}{self.label_str()}'

    def __repr__(self) -> str:
        return str(self)

    # this function is necessary, since it requires the knowledgebase
    def formula_str(self, kb: KnowledgeBase) -> str:
        return f'{self.prefix_str()}{expr_str(self.expr, kb)}'

class PromisedFormula(Formula):
    def __init__(self, kb: KnowledgeBase, expr:Expr, line:str, filename:str, label:str, reason:str):
        super().__init__(kb, expr, line, filename, label, reason, proven=False)   # promised formulas are not proven

# expression
# not a class itself, instead just a type alias
Expr: TypeAlias = list["Expr"] | Token

def deepcopy_expr(expr: Expr) -> Expr:
    if isinstance(expr, Token):
        # Use shallow copy or clone to retain metadata if needed
        return clone_token(expr)
    elif isinstance(expr, list):
        # Recursively copy the sub-expressions
        return [deepcopy_expr(e) for e in expr]
    else:
        assert False, f'Never reach this case!'

# a useful tool for parsing:
T = TypeVar('T')
class PeekableGenerator(Generic[T]):                 # a peekable generator
    def __init__(self, gen: Iterator[T]) -> None:
        self.gen: Iterator[T] = gen                  # the generator
        self.eog: bool        = False                # end-of-generator, are we done yet?
        self.peek: T | None   = None                 # initial peek is None
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

# hierarchical knowledge base
# the level is increased inside blocks and files
# dropping a level drops also all local definitions
Nud: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Token], Expr]
Led: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Expr, Token], Expr]

class KnowledgeBase:
    def __init__(self, parent:KnowledgeBase|None=None) -> None:
        # general
        self.parent: KnowledgeBase|None = parent
        self.level: int            = 0 if parent is None else parent.level + 1
        self.proof: bool           = False                # a proof must be closed by `qed`
        self.libs: list[str]       = []                   # the filenames of loaded libraries

        # syntax
        self.infix:    dict[str, tuple[int,int]] = {}     # left and right binding powers of infix operators
        self.postfix:  dict[str, int]            = {}     # left binding power of postfix operator
        self.prefix:   dict[str, int]            = {}     # right binding power of prefix operator
        self.brackets: dict[str, str]            = {}     # keys are right brackets, values are left brackets
        self.arity:    dict[str, int]            = {}     # for non-zero arities
        self.chain:    dict[str, list[str]]      = {}     # for chaining operators, i.e., 18 = 1+17 <= 20 < 21
        self.bindop:   set[str]                  = set()  # set for variable binding operators
        self.flat:     set[str]                  = set()  # set for declaring a flat operator, i.e., ($a + $b) + $c = $a + $b + $c
        self.sym:      set[str]                  = set()  # set for declaring a symmetric operator, i.e., $a + $b = $b + $a
        self.lbp:      dict[str, int]            = {}     # left binding power
        self.rbp:      dict[str, int]            = {}     # right binding power
        self.alias:    dict[str, str]            = {}     # dict of alias pointing to the original
        self.nud:      dict[str, Nud]            = {}     # null denotation, entries are functions for parsing expressions
        self.led:      dict[str, Led]            = {}     # left denotation, entries are functions for parsing infix expressions

        # variables vs constants
        self.var:      set[str]                  = set()  # set of variables with unused values
        self.const:    set[str]                  = set()  # set of constants with unused values

        # types
        self.bool:     dict[str, list[int]]      = {}     # dict of symbols declared to have boolean output

        # theory
        self.theory: list[Formula] = []                   # list of formulas (axioms added by 'use', 
                                                          #                   assumptions added by 'assume',
                                                          #                   and derived formulas)
        self.show:   list[PromisedFormula] = []           # lists of promised formulas to show

        # misc
        self.format: Format = format_options[1] if parent is None else parent.format  # how formulas look in the shell
        self.verbose: bool  = False if parent is None else parent.verbose           # extra information or not

    def _entry_str(self, keyword:str, key:str, value:str|int|tuple[int,int]|list[int]|list[str]|None = None) -> str:
        if   keyword == 'prefix':   return f'prefix {key} {value}'
        elif keyword == 'infix':    
            if isinstance(value, tuple) and len(value) == 2:
                if key == ' ':
                    return f'infix " " {value[0]} {value[1]}'
                else:
                    return f'infix {key} {value[0]} {value[1]}'
            assert False, f'BUG!  Unexpected value for `infix`, got {value}'
        elif keyword == 'postfix':  return f'postfix {key} {value}'
        elif keyword == 'brackets': return f'brackets {value} {key}'
        elif keyword == 'chain':
            if isinstance(value, list):
                return f'chain {key} {" ".join(map(str, value))}'
            assert False, f'BUG!  Unexpected value for `chain`, got {value}'
        elif keyword == 'arity':    return f'arity {key} {value}'
        elif keyword == 'flat':     return f'flat {key}'
        elif keyword == 'sym':      return f'sym {key}'
        elif keyword == 'bindop':   return f'bindop {key}'
        elif keyword == 'bool':     
            if isinstance(value, list):
                return f'bool {key} {" ".join(map(str, value))}'
            assert False, f'BUG!  Unexpected value for `bool`, got {value}'
        elif keyword == 'var':      return f'var {key}'
        elif keyword == 'const':
            if key == ' ':
                return f'const " "'
            else:
                return f'const {key}'
        elif keyword == 'alias':    return f'alias {key} {value}'
        else: assert False, f'BUG: unknown keyword, got {keyword}'

    def dict_or_set_str(self, keyword: str) -> str:
        some_dict_or_set: dict[str, str|int|tuple[int,int]|list[int]|list[str]] | set[str] = getattr(self, keyword)
        if isinstance(some_dict_or_set, dict):
            lines = [self._entry_str(keyword, key, some_dict_or_set[key]) for key in some_dict_or_set]
        else:
            lines = [self._entry_str(keyword, key) for key in some_dict_or_set]
        lines.sort()
        return '\n'.join(lines)

    def dict_or_set_str_all_levels(self, keyword: str) -> str:
        s: str = ''
        if self.parent is not None:
            s += self.parent.dict_or_set_str_all_levels(keyword) + '\n'
        s += f'; level {self.level}\n'
        s += self.dict_or_set_str(keyword)
        return s

    # SYNTAX RELATED
    def syntax_str_all_levels(self) -> str:
        s = ''
        if self.parent is not None:
            s += self.parent.syntax_str_all_levels() + '\n'
        s += f'; level {self.level}\n'
        all_syntax = [self.dict_or_set_str('prefix'),
                        self.dict_or_set_str('infix'),
                        self.dict_or_set_str('postfix'),
                        self.dict_or_set_str('arity'),
                        self.dict_or_set_str('chain'),
                        self.dict_or_set_str('bindop'),
                        self.dict_or_set_str('brackets'),
                        self.dict_or_set_str('flat'),
                        self.dict_or_set_str('sym'),
                        self.dict_or_set_str('bool')]
        s += '\n'.join([syntax for syntax in all_syntax if syntax != ''])
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
        return s[0] == '$' or s in self.var or (self.parent is not None and self.parent.is_var(s))
    def is_local_var(self, s: str) -> bool:                # check only in the current level, used for `add_const`
        return s in self.var
    def is_bool_var(self, s: str) -> bool:
        # e.g. variable for formulas (in `sub x a A` the symbol `A` is boolean)
        if s[0] == '%':
            return True
        if self.is_var(s):
            return 0 in self.bool_sig(s)
        return False
    def is_const(self, s: str) -> bool:
        return s in self.const   or (self.parent is not None and self.parent.is_const(s))
    def is_alias(self, s: str) -> bool:
        return s in self.alias   or (self.parent is not None and self.parent.is_alias(s))

    def bool_sig(self, s: str) -> list[int]:   # get the bool signature
        if s in self.bool:
            return self.bool[s]
        if self.parent is None:
            return []
        return self.parent.bool_sig(s)

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

    def get_alias(self, s: str) -> str | None:
        if s in self.alias:
            return self.alias[s]
        elif self.parent is not None:
            return self.parent.get_alias(s)
        else:
            return None

    def get_load_level(self, fname: str) -> int | None:
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
            raise KurtException(f'EvalError: arity of symbol "{fun}" has been already set to {self.arity[fun]}')
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

    def add_prefix(self, op: str, rbp: int) -> None:
        if self.is_operator(op) and not self.is_infix(op):    # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self._find_symbol(op)}')
        self.prefix[op] = rbp
        self.nud[op] = lambda ts, kb, op_token: [op_token, parse_expression(ts, kb, rbp)]

    def add_infix(self, op: str, lbp: int, rbp: int) -> None:
        if self.is_operator(op) and not self.is_prefix(op):   # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self._find_symbol(op)}')
        self.infix[op] = (lbp, rbp)                           # to nicely list all operators
        self.led[op] = lambda ts, kb, left, op_token: [op_token, left, parse_expression(ts, kb, rbp)]
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_postfix(self, op: str, lbp: int) -> None:
        if self.is_operator(op):
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self._find_symbol(op)}')
        self.postfix[op] = lbp                                # to nicely list all operators
        def led(_ts: PeekableGenerator, _kb: KnowledgeBase, left: Expr, op_token: Token) -> Expr:
            return [op_token, left]
        self.led[op] = led
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_chain(self, op: str, chain: list[str]) -> None:
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator "{op}" must be infix operator to declare chain')
        for c in chain:
            if not self.is_infix(c):
                raise KurtException(f'EvalError: operator "{c}" must be infix operator to declare chain')
        if len(chain) < 1:
            raise KurtException(f'EvalError: chain of operators must have at least two elements')
        self.chain[op] = chain

    def add_bindop(self, fun: str) -> None:
        if fun not in self.arity:
            raise KurtException(f'EvalError: before declaring symbol "{fun}" as variable binding, you must set its arity')
        if self.arity[fun] < 2:
            raise KurtException(f'EvalError: arity of binding operators must be at least 2')
        self.bindop.add(fun)

    def add_flat(self, op: str) -> None:
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator "{op}" must be infix operator to declare flatness')
        if self.is_flat(op):
            raise KurtException(f'EvalError: operator "{op}" is already declared "flat"')
        self.flat.add(op)

    def add_sym(self, op) -> None:
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator "{op}" must be infix operator to declare symmetry')
        if self.is_sym(op):
            raise KurtException(f'EvalError: operator "{op}" is already declared "sym"')
        self.sym.add(op)

    def add_brackets(self, lbracket, rbracket) -> None:
        if self.is_operator(lbracket) or self.is_const(lbracket) or self.is_var(lbracket):
            raise KurtException(f'EvalError: symbol "{lbracket}" already exist as {self._find_symbol(lbracket)}')
        if self.is_operator(rbracket) or self.is_const(rbracket) or self.is_var(rbracket):
            raise KurtException(f'EvalError: symbol "{rbracket}" already exist as {self._find_symbol(rbracket)}')
        self.add_const(lbracket)              # brackets must be new constants
        self.add_const(rbracket)
        self.brackets[rbracket] = lbracket    # to list the brackets (not used for parsing)
        def nud(ts: PeekableGenerator, kb: KnowledgeBase, t: Token) -> Expr:
            expr: Expr = parse_expression(ts, kb, bracket_rbp)
            token: Token = next(ts)
            if token.label == 'END':
                raise StopIteration
            if token.value != rbracket: 
                raise KurtException(f'SyntaxError: expected "{rbracket}"', column=token.column)
            token.value = f'{lbracket}$$${rbracket}'    # use a value that can not come from the tokenizer, avoid space for readability
            return [token, expr]
        self.nud[lbracket] = nud
        self.lbp[rbracket] = bracket_lbp

    def add_var(self, s: str) -> None:
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already used as a constant')
        self.var.add(s)

    def add_const(self, s: str) -> None:
        # a constant is automatically declared if a new symbol is used or when it is explicitly declared
        # declaring is only allowed, if it doesn't yet exist as a variable or constant
        if self.is_local_var(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a variable on this level or starts with "$"')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a constant and can not be declared freshly again')
        self.const.add(s)

    def add_alias(self, s: str, t: str) -> None:
        if self.is_var(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a variable or starts with $')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a constant')
        self.alias[s] = t         # add a key `s` with value `t`

    def add_bool(self, s: str, v: list[int]) -> None:
        if len(self.bool_sig(s)) > 0:
            raise KurtException(f'EvalError: symbol "{s}" is already declared bool')
        if self.is_bindop(s) and 1 in v:
            raise KurtException(f'EvalError: the first position of binding operators can not be declared boolean')
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

    def get_lbp(self, token: Token|None) -> int:
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

    # THEORY RELATED
    def all_theory(self) -> Iterator[Formula]:
        # iterate over all levels
        for f in reversed(self.theory):
            debug(f)
            yield f
            # can we chop of universal quantifier?
            while is_forall(f.simplified_expr):
                f = f.clone(self)
                assert isinstance(f.simplified_expr, list) and len(f.simplified_expr) == 3
                f.simplified_expr = f.simplified_expr[2]
                debug(f)
                yield f
        if self.parent is not None:
            yield from self.parent.all_theory()

    def theory_str(self, op:str|None=None) -> str:
        s: str = self.parent.theory_str(op) if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.theory:
            if op is None or is_op_expr(f.expr, op):
                s += f'{f.formula_str(self)}\n'
        return s

    def _add_new_symbols(self, e: Expr, bound_vars: set[str] = set()) -> None:
        match e:
            case Token(label='SYMBOL', value=s) if isinstance(s, str) and self.is_var(s):
                pass                  # do nothing
            case Token(label='SYMBOL', value=s) if isinstance(s, str) and self.is_bool_var(s):
                pass                  # do nothing
            case Token(label='SYMBOL', value=s) if isinstance(s, str) and self.is_const(s):
                pass                  # do nothing
            case Token(label='SYMBOL', value=s) if isinstance(s, str):
                if s not in bound_vars:
                    self.add_const(s)     # create a new constant symbol
            case [*children]:
                match children:
                    case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=v), *tail]:
                        if op in self.bindop:
                            assert isinstance(v, str), f'BUG: symbol must be string'
                            bound_vars.add(v)
                for child in children:
                    self._add_new_symbols(child, bound_vars)
            case _:
                pass                  # do nothing

    def theory_append(self, f: Formula, symbol_level_prev: bool = False) -> None:
        if symbol_level_prev:
            # add the symbols to the previous level
            assert self.parent is not None, f'BUG: can not add symbols one level up, check `assume` implementation'
            self.parent._add_new_symbols(f.expr)
        else:
            self._add_new_symbols(f.expr)
        self.theory.append(f)

    def show_append(self, f: PromisedFormula) -> None:
        self._add_new_symbols(f.expr)
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

initial_kb.add_const (TRUE_SYMBOL)                         # true is const symbol
initial_kb.add_const (IMPL_SYMBOL)                         # implies is const symbol
initial_kb.add_const (AND_SYMBOL)                          # and is const symbol
initial_kb.add_bool  (TRUE_SYMBOL, [0])                    # true is bool
initial_kb.add_bool  (IMPL_SYMBOL, [0, 1, 2])              # implies is bool with bool input
initial_kb.add_bool  (AND_SYMBOL,  [0, 1, 2])              # and is bool with bool inputs
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
        if s[0] == '(' and s[-1] == ')':
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

def compare_expr(t1: Expr, t2: Expr) -> int:                                # "less than" for expressions
    if isinstance(t1, Token) and isinstance(t2, list):
        return -1                                        # e.g. 17 < [1,2]
    elif isinstance(t1, list) and isinstance(t2, Token):
        return 1                                         # e.g. [1,2] < 17
    elif isinstance(t1, Token) and isinstance(t2, Token):
        if t1 < t2:
            return -1
        elif t1 > t1:
            return 1
        else:
            return 0
    else:
        assert isinstance(t1, list) and isinstance(t2, list), f'BUG: expression is either a list or token'
        if len(t1) < len(t2):
            return -1
        elif len(t1) > len(t2):
            return 1
        else:
            for (s1, s2) in zip(t1, t2):
                c = compare_expr(s1, s2)
                if c == 0:
                    continue
                return c
            return 0

def first_var(expr: Expr, kb: KnowledgeBase) -> str:
    match expr:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and not kb.is_var(s):
            return s
        case [head, *tail]:
            return first_var(head, kb)
        case _:
            assert False, 'empty expression?'

def simplify(expr: Expr, kb: KnowledgeBase) -> Expr:
    for op in kb.flat:
        expr = flatten_op(op, expr)       # flatten certain operators
    return expr

# special tokens that are made for the parser and sometimes artificially generated
space_token: Token = Token('SYMBOL', SPACE_SYMBOL)  # for expressions like 'f x'
end_token:   Token = Token('END', '$$$')            # for the end of a string

# extract all special symbols from the replacement values
SPECIAL_SYMBOLS = ''.join(sorted(set(''.join(REPLACEMENTS.values()))))

# scanner based on regular expressions (let's support unicode!)
# note that the ordering of the expressions here is important
scanner: re.Pattern = re.compile(fr'''
  (?P<COMMENT> [;].*$)                           | # comments
  (?P<FLOAT>   [0-9]+\.[0-9]+)                   | # floating point literals
  (?P<INT>     [0-9]+)                           | # integer literals
  (?P<STRING>  ["][^"]*["])                      | # string literals
  (?P<SYMBOL>  [$%@]?[A-Za-z][A-Za-z0-9]*        | # symbols 1: identifiers with at most one leading '$' or '%' or '@'
               [()]                              | # symbols 2: round brackets
               [,]                               | # symbols 3: comma
               [.]                               | # symbols 4: dot for namespaces
               [:=+\-*/#&^'∈!<>{{}}[\]|_]+       | # symbols 5: standard operators including literal {{ }}
               [{re.escape(SPECIAL_SYMBOLS)}])   | # symbols 6: logic, Greek and other math symbols (always single char)
  (?P<NEWLINE> [\n])                             | # newline
  (?P<WHITE>   [^\S\n\r]+)                       | # whitespace (not newline)
  (?P<ERROR>   .)                                  # anything else is an error
''', re.VERBOSE | re.MULTILINE)
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
            alias:  str | None = kb.get_alias(value)
            origin: str | None = None
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
        elif label == 'ERROR':  # error
            raise KurtException(f'SyntaxError: scanning error while scanning "{value}"', column)
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
        raise KurtException(f'SyntaxError: token "{t.value}" cannot start an expression', t.column)
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

def sort_exprs(exprs: list[Expr]) -> list[Expr]:
    return sorted(exprs, key=functools.cmp_to_key(compare_expr))

def sort_symmetric_ops(kb: KnowledgeBase, expr: Expr) -> Expr:                        # symmetric operators can sort their args
    if isinstance(expr, list):
        expr = [sort_symmetric_ops(kb, e) for e in expr] # start inside
        if (isinstance(expr[0], Token) 
            and expr[0].label == 'SYMBOL' 
            and isinstance(expr[0].value, str) 
            and kb.is_sym(expr[0].value) 
            and expr[0].value != SPACE_SYMBOL):  # we exclude the SPACE_SYMBOL, even though it is symmetric
            expr = [expr[0]] + sort_exprs(expr[1:])
        return expr
    elif isinstance(expr, Token):
        return expr
    else:
        assert False, f'BUG: expression must be list or Token, got {expr_str(expr, kb)}'

def flatten_op(flat_op: str, expr: Expr) -> Expr:                                # flatten nested 'op'-expressions
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

def group_by_arity(expr: Expr, kb: KnowledgeBase) -> tuple[Expr, list[Expr]]:
    # input: `expr` which is a list of functions and arguments
    # output: `e` which is properly group and the `tail` which is the rest of non-eaten arguments
    match expr:
        case [Token(label='SYMBOL', value=op), *tail] if isinstance(op, str) and ((arity:=kb.get_arity(op)) > 0):
            e: Expr = [expr[0]]                                       # the new expression
            for i in range(1, arity+1):
                if len(tail) == 0:
                    raise KurtException(f'EvalError: not enough arguments for "{op}"')
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

def check_no_keyword(expr: Expr) -> None:
    match expr:
        case Token(label='SYMBOL', value=v) if v in keywords or v in helper_keywords:
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
    check_no_keyword(tail)             # don't check the `keyword` and the `label`
    return tail, label

def post_process(kb: KnowledgeBase, expr: Expr) -> tuple[Expr, str]:
    expr = flatten_op(SPACE_SYMBOL, expr)               # flatten all space operators
    expr = process_arity(expr, kb)                      # turns space operators into function calls according to arities
    expr = remove_round_brackets(expr)                  # remove round brackets for grouping
    expr, label = check_expr_label(expr, kb)       # check and split `expr` and `label`
    expr = simplify(expr, kb)                           # simplify the expression, basically flattening

    return expr, label

def parse_tokenstream(ts: PeekableGenerator, kb: KnowledgeBase) -> tuple[Token|None, Expr, str]:
    assert isinstance(ts.peek, Token)
    keyword_token: Token | None
    keyword: str
    label: str
    if ts.peek.label == 'SYMBOL' and ts.peek.value in keywords:
        keyword  = ts.peek.value
        keyword_token = next(ts)                              # remove a keyword right away early
    else:
        keyword = ''
        keyword_token = None
    if ts.peek.label == 'END': 
        return keyword_token, [], ''                          # empty token stream
    if keyword_token is None or keyword_token.value in keywords_with_parsing:
        expr: Expr
        expr        = parse_expression(ts, kb, begin_rbp)     # parse expression
        expr, label = post_process(kb, expr)                  # turn spaces into calls, symmetry, flatness
        if keyword == 'thus':
            # type check with the parent
            if kb.parent is None:
                raise KurtException(f'EvalError: "thus" can only be used after "fix", "take", or "assume"')
            kb = kb.parent
        type_check_expression(expr, kb)                       # (some) type checking
    else:
        expr = list(ts)[:-1]                                  # [:-1] removes end_token
        label = ''
    return keyword_token, expr, label

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

def increase_level(kb:KnowledgeBase) -> KnowledgeBase:
    return KnowledgeBase(parent=kb)

def decrease_level(kb:KnowledgeBase) -> KnowledgeBase:
    if kb.level == 0:
        raise KurtException(f'EvalError: no block to close')
    if len(kb.show) > 0:                  # any planned formulas inside the current proof?
        raise KurtException(f'ProofError: planned formula "{expr_str(kb.show[-1].expr, kb)}" in current proof is unproven')
    assert kb.parent is not None, f'BUG: we should be one level up'
    return kb.parent                        # drop current level

def _extract_new_consts(expr: Expr, kb: KnowledgeBase) -> list[str]:
    # extract all new constants from the expression
    match expr:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and not kb.is_const(s):
            return [s]        # new constant found
        case [*children]:
            new_consts = []
            for child in children:
                new_consts += _extract_new_consts(child, kb)
            return new_consts
    return []

def extract_one_new_const(expr: Expr, kb: KnowledgeBase) -> str:
    # extract exactly one new constant from the expression and checks there is only one
    new_consts = _extract_new_consts(expr, kb)
    if len(new_consts) != 1:
        raise KurtException(f'EvalError: expected exactly one new constant, got {len(new_consts)} in "{expr_str(expr, kb)}"')
    return new_consts[0]

def extract_zero_new_consts(expr: Expr, kb: KnowledgeBase) -> None:
    new_consts = _extract_new_consts(expr, kb)
    if len(new_consts) != 0:
        raise KurtException(f'EvalError: expected no new constants, got {len(new_consts)} in "{expr_str(expr, kb)}"')

def eval_use(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool, symbol_level_prev: bool=False) -> KnowledgeBase:
    if not bool_expr(expr, kb):
        raise KurtException(f'EvalError: must evaluate to boolean, got "{expr_str(expr, kb)}"')
    reason = 'without proof'
    if len(label) > 0:
        reason += f' "{label}"'
    reason = decorate_reason(mainstream, reason, filename, str(line))
    f = Formula(kb, expr, str(line), filename, label, reason, proven=False)
    kb.theory_append(f, symbol_level_prev)
    if mainstream:
        log(f.formula_str(kb), reason, kb.level)
    return kb

def eval_show(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    if not bool_expr(expr, kb):
        raise KurtException(f'EvalError: must evaluate to boolean, got "{expr_str(expr, kb)}"')
    reason = decorate_reason(mainstream, 'claim', filename, str(line))
    if len(label) > 0:
        reason += f' "{label}"'
    f = PromisedFormula(kb, expr, str(line), filename, label, reason)
    kb.show_append(f)
    if mainstream:
        log(f'show {expr_str(expr, kb)}', reason, kb.level)
    return kb

def eval_proof(kb: KnowledgeBase, mainstream: bool) -> KnowledgeBase:
    if len(kb.show) == 0:
        raise KurtException(f'ProofError: can not start proof since there is no planned formula on current level')
    if mainstream:
        log('proof', '', kb.level)
    kb = increase_level(kb)          # add a new level/scope to the knowledgebase
    kb.proof = True
    return kb

def eval_def(kb: KnowledgeBase, expr: Expr, label: str, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    match expr:
        case [Token(label='SYMBOL', value=s), LHS, RHS] if isinstance(s, str) and (s== EQUAL_SYMBOL or s==IFF_SYMBOL):
            lhs_const = extract_one_new_const(LHS, kb)  # extract exactly one new constants from the left-hand side
            extract_zero_new_consts(RHS, kb)                 # check there are no new constants on the right-hand side
        case _:
            raise KurtException(f'EvalError: `def` only allowed with `{EQUAL_SYMBOL}` and `{IFF_SYMBOL}`, got "{expr_str(expr, kb)}"')
    kb = eval_use(kb, expr, label, filename, line, mainstream=False)  # use the expression as a definition
    if mainstream:
        reason = f'{line} defining `{lhs_const}`'
        log(f'def {expr_str(expr, kb)}', reason, kb.level-1)  # log the new constant
    return kb

def eval_openblock(kb: KnowledgeBase, line: int, mainstream: bool) -> KnowledgeBase:
    if mainstream:
        reason = f'{line} open local scope'
        log('openblock', reason, kb.level)
    kb = increase_level(kb)          # add a new level/scope to the knowledgebase
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
            if s in symbols:
                debug(s)
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
    # `thus` is closing a block opened by `consider`, but also for `not-intro`, `forall-intro`, `impl-intro`, `exists-elim`

    # check that there are no constant symbols on this level appearing in `expr`
    # (1) for `assume` (not-intro and impl-impl) create new constants already on the level below
    # (2) for `fix` and `pick` (forall-intro) create new constants on the new level

    # the constants on the current level are not allowed, however, the variables of the previous level are allowed (see `de-morgan.kurt`)
    assert kb.parent is not None
    not_allowed = kb.const - kb.parent.all_vars()   # set difference creating new set
    if contains(expr, not_allowed, kb):
        raise KurtException(f'ProofError: there are constant symbols on the current level appearing in the conclusion of `thus`, got `{expr_str(expr, kb)}`')

    # try to derive `expr` depending on its form
    if is_not(expr):
        reason = not_intro(expr, kb)
    elif is_forall(expr):
        reason = forall_intro(expr, kb)
    elif is_implication(expr):
        reason = impl_intro(expr, kb)
    else:
        # finally `exists-elim`
        # (1) check there are no assumptions
        unproven_exprs = [f.expr for f in kb.theory if f.proven == False]
        if len(unproven_exprs) > 0:   # (i)
            raise KurtException(f'ProofError: there are assumptions on the current level, `thus` can thus only conclude an implication or an universal quantified formula to close the block, got "{expr_str(unproven_exprs[-1], kb)}"')
        # (2) derive the expression
        reasons = derive_expr(expr, kb, filename, mainstream)       # this might generate a KurtException
        reason  = ' '.join(reasons) if len(reasons) > 0 else ''  # join all reasons
        reason += f', then by "exist-elim"'
    reason = decorate_reason(mainstream, reason, filename, str(line))
    label = ''
    f = Formula(kb, expr, str(line), filename, label, reason, proven=True)
    kb = decrease_level(kb)                    # drop current level and perform some checks
    kb.theory_append(f)                        # add a copy to the theory
    if mainstream:
        log('thus ' + f.formula_str(kb), reason, kb.level)
    return kb

def _first_or_none(xs: Iterator[Subst]) -> Subst | None:
    return next(iter(xs), None)

def eval_qed(kb: KnowledgeBase, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    parent = kb.parent
    if not kb.proof  or  parent is None:
        raise KurtException(f'EvalError: no proof to finish, `qed` can only appear at the end of a `proof` block')
    assert len(parent.show) > 0, f'BUG: no planned formula on previous level, this should have been already checked when calling "proof"'
    planned_expr = parent.show[-1].expr        # peek at the last planned formula from previous level
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: no formula has been proven, `qed` can only be used after a successful proof')
    proven_expr  = kb.theory[-1].expr          # what actually has been proven
    reason = ''
    optional_subst = _first_or_none(_implies(proven_expr, planned_expr, kb))
    if optional_subst is None:
        raise KurtException(f'ProofError: planned formula "{expr_str(planned_expr, kb)}" does not match the last formula in the theory "{expr_str(proven_expr, kb)}"')
    reason = decorate_reason(mainstream, reason, filename, str(line))
    label = ''
    f = Formula(kb, planned_expr, str(line), filename, label, reason, proven=True)
    kb = decrease_level(kb)                    # drop current level and perform some checks
    kb.show.pop()                              # pop the last planned formula off the show stack, since it is proved now
    kb.theory_append(f)                        # add a copy to the current theory
    if mainstream:
        log('qed', '', kb.level)
        #log(f.formula_str(kb), reason, kb.level)
    return kb

def eval_fix(kb: KnowledgeBase, expr: Expr, filename: str, line: int, mainstream: bool, new_level: bool=True) -> KnowledgeBase:
    with_condition = isinstance(expr, list) and bool_expr(expr, kb)
    if with_condition:
        new_const = extract_one_new_const(expr, kb)  # extract exactly one new constant from the expression
    else:
        match expr:
            case Token(label='SYMBOL', value=new_const) if isinstance(new_const, str):
                pass
            case _:
                raise KurtException(f'EvalError: expression must be new constant or boolean condition with new constant, got "{expr_str(expr, kb)}"')
    assert isinstance(new_const, str)
    if new_level:
        kb = eval_openblock(kb, line, mainstream=False)  # open a new block
    kb.add_const(new_const)          # add the new constant to the knowledgebase
    if with_condition:
        kb = eval_use(kb, expr, 'fix', filename, line, mainstream=False)  # use the expression as an assumption
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
    debug(f'fact == {fact}')

    # (2) check that the `fact` matches some existential statement in the theory so far
    for candidate in kb.all_theory():
        cand_expr = candidate.simplified_expr
        if is_exists(cand_expr):
            match cand_expr:
                case [Token(label='SYMBOL', value=EXIST_SYMBOL), Token(label='SYMBOL', value=bound_var), body] if isinstance(bound_var, str):
                    subst: Subst = {bound_var: new_const_expr}
                    body = deepcopy_expr(body)
                    body = apply_subst(body, subst, kb)
                    debug(f'body == {body}')
                    if equal_expr(body, fact):
                        break  # end the loop without the `else` block
    else:
        raise KurtException(f'ProofError: can not find an existential formula that matches the `pick`')

    # (3) open a new block, add a new constant and the fact
    kb = eval_openblock(kb, line, mainstream=False);    # open a new block
    kb.add_const(new_const)                            # add the new constant to the knowledgebase
    reason = f'added as a fact for witness `{new_const}`'
    f = Formula(kb, fact, str(line), filename, label, reason, proven=True)
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
        match args:
            case [Token(label='STRING', value=fname)]:
                assert isinstance(fname, str)
                kb = load_file(fname, kb, path=local_path, mainstream=False)
            case _:
                raise KurtException(f'ParseError: "{keyword}" takes a string for the filename', keyword_token.column)
    elif keyword == 'parse':
        if len(args) > 0:
            tokenlist: Expr = args + [end_token]                               # add end token for parse_expression
            ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))  # turn list into peekable generator
            expr = parse_expression(ts, kb, begin_rbp)                         # parse the tokenlist
            expr, label = post_process(kb, expr)                               # turn spaces into calls, symmetry
            msg = f'{expr_sexpr(expr)}'
            if len(label) > 0:
                msg += f' "{label}"'
            print(msg, file=sys.stdout)
    elif keyword == 'tokenize':
        if len(args) > 0:
            tokenlist: Expr = args + [end_token]                               # add end token for parse_expression
            ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))  # turn list into peekable generator
            msg = f'{"  ".join([str(t) for t in ts])}'
            print(msg, file=sys.stdout)
    elif keyword == 'format':
        match args:
            case []:
                print(kb.format, file=sys.stdout)
            case [Token(label='SYMBOL', value=option)] if option in format_options:
                kb.format = option
            case _:
                raise KurtException(f'only a single arg out of {format_options} is allowed"')
    elif keyword == 'level':
        if len(args) > 0:
            raise KurtException(f'ParseError: "{keyword}" does not take any arguments', keyword_token.column)
        print(kb.level, file=sys.stdout)

    # SYNTAX RELATED
    elif keyword == 'syntax':
        if len(args) > 0:
            raise KurtException(f'ParseError: "{keyword}" does not take any arguments', keyword_token.column)
        else:
            print('; syntax')
            print(kb.syntax_str_all_levels(), file=sys.stdout)
    elif keyword == 'prefix':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=rbp)]:
                assert isinstance(op, str)
                assert isinstance(rbp, int)
                kb.add_prefix(op, rbp)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'INT']])
                raise KurtException(f'ParseError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'postfix':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=lbp)]:
                assert isinstance(op, str)
                assert isinstance(lbp, int)
                kb.add_postfix(op, lbp)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'INT']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'infix':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=lbp), Token(label='INT', value=rbp)]:
                assert isinstance(op, str)
                assert isinstance(lbp, int)
                assert isinstance(rbp, int)
                kb.add_infix(op, lbp, rbp)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'INT', 'INT']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'arity':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op), Token(label='INT', value=arity)]:
                assert isinstance(op, str)
                assert isinstance(arity, int)
                kb.add_arity(op, arity)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'INT']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'brackets':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=lbracket), Token(label='STRING'|'SYMBOL', value=rbracket)]:
                kb.add_brackets(lbracket, rbracket)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'bindop':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_bindop(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'chain':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op), *tail]:
                assert isinstance(op, str)
                chain: list[str] = []
                for t in tail:
                    assert isinstance(t, Token) and t.label=='SYMBOL' and isinstance(t.value, str)
                    chain.append(t.value)
                kb.add_chain(op, chain)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'STRING'], ['STRING', 'STRING', 'STRING'], ['STRING', 'STRING', 'STRING', 'STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'flat':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_flat(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'sym':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                kb.add_sym(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'bool':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
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
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_var(op)
                if mainstream:
                    log(f'var {op}', f'added variable', kb.level)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)

    elif keyword == 'const':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_const(op)
                if mainstream:
                    log(f'const {op}', f'added constant', kb.level)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'alias':
        match args:
            case []:
                print(kb.dict_or_set_str_all_levels(keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=s), Token(label='STRING'|'SYMBOL', value=t)]:
                assert isinstance(s, str) and isinstance(t, str)
                kb.add_alias(s, t)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)

    # THEORY AND PROOF RELATED
    elif keyword == 'theory':
        if len(args) > 0:
            msg = create_usage(keyword, [[]])
            raise KurtException(f'EvalError: {keyword} does not take any arguments', keyword_token.column)
        print(kb.theory_str(), file=sys.stdout)
    elif keyword == 'find':
        if len(args) > 0:
            tokenlist: Expr = args + [end_token]                                        # add end token for parse_expression
            ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))           # turn list into peekable generator
            expr: Expr
            expr = parse_expression(ts, kb, begin_rbp)                                  # parse the tokenlist
            expr, label = post_process(kb, expr)                                        # turn spaces into calls, symmetry
            expr_alt, subst = rename_all_vars(expr, {}, kb)  # rename all variables
            subst_back: dict[str, str] = {}
            for k in subst.keys():
                v = subst[k]
                if isinstance(v, Token) and isinstance(v.value, str):
                    subst_back[v.value] = k
            for candidate in kb.all_theory():
                # iterate over all possible substitutions that create a match
                for subst_cand in match_exprs([(candidate.simplified_expr, expr_alt)], {}, kb):
                    subst_str = f'{expr_str(expr, kb)} '
                    subst_str += 'with ' 
                    subst_str += ', '.join([f'{subst_back[var]}={expr_str(subst_cand[var], kb)}' for var in subst_cand])
                    log(expr_str(candidate.expr, kb), subst_str, kb.level)
    elif keyword == 'implications':
        if len(args) > 0:
            msg = create_usage(keyword, [[]])
            raise KurtException(f'EvalError: {keyword} does not take any arguments', keyword_token.column)
        print(kb.theory_str(op=IMPL_SYMBOL), file=sys.stdout)
    elif keyword == 'use':
        if len(args) == 0:
            print(kb.theory_str(), file=sys.stdout)
        else:
            expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
            kb = eval_use(kb, expr, label, filename, line, mainstream)  # use the expression as an assumption
    elif keyword == 'thus':
        if len(args) == 0:
            raise KurtException(f'EvalError: `{keyword}` takes an expression as argument')
        expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
        kb = eval_thus(kb, expr, label, filename, line, mainstream)  # use the expression as a conclusion
    elif keyword == 'break':
        if len(args) > 0:
            raise KurtException(f'EvalError: `{keyword}` does not take any arguments')
        kb = decrease_level(kb)                    # drop current level and perform some checks
        if mainstream:
            log('break', f'{line} forget the last proof or local scope', kb.level)
    elif keyword == 'show':
        if len(args) == 0:
            print(kb.show_str(), file=sys.stdout)
        else:
            expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
            kb = eval_show(kb, expr, label, filename, line, mainstream)
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
        kb = eval_openblock(kb, line, mainstream=False)  # open a new block
        expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
        kb = eval_use(kb, expr, label, filename, line, mainstream=False, symbol_level_prev=True)  # use the expression as an assumption
        if mainstream:
            reason = f'{line} open local scope with assumption'
            log(f'{keyword} {expr_str(expr, kb)}', reason, kb.level-1)  # log the new constant
    elif keyword == 'def':
        if len(args) == 0:
            print(kb.theory_str(), file=sys.stdout)
        else:
            expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
            kb = eval_def(kb, args, label, filename, line, mainstream)  # use the expression as a definition
    elif keyword == 'fix':
        msg = 'EvalError: `fix` takes new constants or boolean expressions'
        if len(args) == 0:
            raise KurtException(msg)
        if is_comma_separated_list(args):
            args = args[1:]    # remove the comma operator

        # add the new constants and their constraints (if boolean expressions are given)
        new_level = True
        for expr in args:  # args is a list of expressions
            kb = eval_fix(kb, expr, filename, line, mainstream, new_level) # only open a new block in the first iteration)
            new_level = False  # keep the level for the next iteration of the for loop
        if mainstream:
            reason = f'{line} open local scope with (possibly constrained) new constants'
            args_str = [expr_str(expr, kb) for expr in args]
            log(f'{keyword} {", ".join(args_str)}', reason, kb.level-1)  # log the new constants
    elif keyword == 'pick':
        msg = 'EvalError: `pick` takes a new constant, keyword `with` and a formula , e.g. `pick x with F(x)`'
        if len(args) == 0:
            raise KurtException(msg)
        match args:
            case [Token(label='SYMBOL', value=new_const), Token(label='SYMBOL', value='with'), *fact_expr] if isinstance(new_const, str) and not kb.is_const(new_const):
                kb, fact = eval_pick(kb, args[0], fact_expr, filename, line, mainstream)
            case _:
                raise KurtException(msg)
        if mainstream:
            reason = f'{line} open local scope with new constant `{new_const}`'
            log(f'{keyword} {new_const} with {expr_str(fact, kb)}', reason, kb.level-1)  # log the new constants
    else:
        assert False, f'BUG: unknown keyword, got "{keyword}"'

    # finally return the possibly modified knowledgebase
    return kb

def letter_generator() -> Iterator[str]:
    letters = 'abcdefghijklmnopqrstuvwxyz'
    for size in itertools.count(1):
        for combo in itertools.product(letters, repeat=size):
            yield ''.join(combo)

def eval_expression(keyword_token: Token|None, expr: Expr, label: str, kb: KnowledgeBase, line: int, filename: str, mainstream: bool) -> KnowledgeBase:
    if keyword_token is None:
        # expression without keyword: try to derive the formula and add it to the theory
        if expr==[]:
            return kb
        if not bool_expr(expr, kb):
            raise KurtException(f'EvalError: must evaluate to boolean, got "{expr_str(expr, kb)}"')
        reasons = derive_expr(expr, kb, filename, mainstream)  # this might raise ProofError exceptions
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
                sub_f = Formula(kb, clause, line_str, filename, label, reason, proven=True)
                kb.theory_append(sub_f)                         # add sub to the knowledge base
                if mainstream:
                    log(sub_f.formula_str(kb), reason, kb.level)
            reason = decorate_reason(mainstream, f'by {", ".join(line_strs)} "and-intro"', filename, str(line))
        label = ''
        f = Formula(kb, expr, str(line), filename, label, reason, proven=True)
        kb.theory_append(f)                         # add it to the knowledge base
        if mainstream:
            log(f.formula_str(kb), reason, kb.level)
        return kb
    else:
        if not isinstance(expr, list):
            expr = [expr]
        match keyword_token:
            case Token(label='SYMBOL', value=v) if v in ['parse', 'tokenize', 'fix', 'let', 'take']:
                kb = eval_keyword_expression(keyword_token, expr, label, kb, line, filename, mainstream)
            case _:
                # iterate over the expr to allow ',' in keyword expressions
                args = []
                for e in expr:
                    match e:
                        case Token(label='SYMBOL', value=v) if v==COMMA_SYMBOL:
                            if len(args) == 0:
                                raise KurtException(f'ParseError: nothing to separate with a comma, comma can not be used with `use`, `assume`, `show`, etc.')
                            kb = eval_keyword_expression(keyword_token, args, label, kb, line, filename, mainstream)
                            args = []
                        case _:
                            args.append(e)
                kb = eval_keyword_expression(keyword_token, args, label, kb, line, filename, mainstream)
        return kb

########################
## kurt type checking ##
########################

def bool_expr(expr: Expr, kb: KnowledgeBase) -> bool:
    match expr:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_bool_var(v):
            return True                    # boolean variables
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and not kb.is_bool_var(v):
            return 0 in kb.bool_sig(v)
        case [Token(label='SYMBOL', value=v), *tail] if v==SUB_SYMBOL:
            return bool_expr(tail[2], kb)
        case [Token(label='SYMBOL', value=v), *_]:
            return bool_expr(expr[0], kb)
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
    match expr:

        # substitutions are always boolean
        case [Token(label='SYMBOL', value=v), *_] if v==SUB_SYMBOL:
            pass

        # most expressions: prefix, postfix, infix, bindop, ...
        case [Token(label='SYMBOL', value=op), *tail]:
            assert isinstance(op, str)
            for idx in range(1, len(tail)+1):
                if idx in kb.bool_sig(op) and not bool_expr(tail[idx-1], kb):
                    raise KurtException(f'TypeError: arg number {idx} of `{op}`, i.e., `{expr_str(tail[idx-1], kb)}` must be boolean', column=expr_column(tail[idx-1]))
            if kb.is_bindop(op):
                # check that the first argument is either a variable or a boolean expression
                match tail[0]:
                    case Token(label='SYMBOL', value=v):
                        if not isinstance(v, str):
                            raise KurtException(f'TypeError: first arg of binding operator must be boolean or new symbol, got {v}', column=expr_column(tail[0]))
                        if kb.is_const(v):
                            raise KurtException(f'TypeError: first arg of binding operator must not be constant, got a constant "{v}"', column=expr_column(tail[0]))
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
#    e.g. `a = b` and `F // x=a` leads to `F // x=b`
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

# "negation-intro"
#
# assume A
#    bla
#    bottom
# thus not A    ; neg-intro

def negation_intro(expr: Expr, kb: KnowledgeBase) -> str:
    return 'not yet'

# "forall-intro" without condition
#
#       fix ε           ; or use `let` or `take`
#         bla bla
#         F(ε)
#       thus ∀ε F(ε)    ; forall-intro
# which is short for
#       consider
#         const ε         ; on this level now `ε` is constant
#         bla bla
#         F(ε)
#       thus ∀ε>0 F(ε)    ; checks whether there are 
# ensure that the current level contains only ε as a new symbol and nothing else (also no assumptions)

def forall_intro(expr: Expr, kb: KnowledgeBase) -> str:

    # step 0: ensure we are one level up
    if kb.level == 0:
        raise KurtException(f'EvalError: forall-intro requires one level up')
    assert kb.parent is not None
    kb_parent: KnowledgeBase = kb.parent

    # step 1: dissect the forall quantified expression
    # - chop off forall quantifiers from `expr` until we can not find the corresponding new constant
    # - collect the chopped-off new constants
    # - collect the chopped-off premises
    # - ensure we get at least one constant
    the_consts: list[str] = []
    conditions: list[Expr] = []    # the list `the_consts` and `conditions` can have different lengths
    body = expr  # this is the loop variable, where we will chop off the forall quantifiers
    while True:
        match body:
            case [Token(label='SYMBOL', value=op), bound_v_expr, inner_body] if op == FORALL_SYMBOL:
                match bound_v_expr:
                    case Token(label='SYMBOL', value=the_const) if isinstance(the_const, str):
                        if the_const not in kb.const:      # check whether `the_const` is a new constant on the current level
                            if len(the_consts) > 0:
                                break # we have found some forall quantifiers with new constants, some quantifiers will remain in the `body`
                            else:
                                raise KurtException(f'EvalError: at least one new constant must be defined on this level, use `fix`, `let`, or `take` to define it')
                        the_consts.append(the_const)  # collect the new constant
                        # no condition to add
                    case [*condition]:
                        the_const = extract_one_new_const(condition, kb_parent)  # extract `the_const` that was new one level up
                        the_consts.append(the_const)  # collect the new constant
                        conditions.append(condition)    # collect the premise
                    case _:
                        raise KurtException(f'SyntaxError: bounded variable expected or condition expected, got {bound_v_expr}')
                body = inner_body  # continue with the body of the forall, this is the loop increment
            case _:
                break
    assert len(the_consts) > 0, f'BUG, the call to `forall-intro` requires `expr` to be a forall-expression'
    # now we continue with `the_consts`, `conditions` and `body`

    # step 2: check that all assumptions on the current level correspond to the conditions
    assumptions: list[Expr]
    assumptions = [f.expr for f in kb.theory if f.proven == False]  # collect all assumptions on the current level
    if len(assumptions) != len(conditions):
        raise KurtException(f'EvalError: number of assumptions ({len(assumptions)}) on the current level must match the number of conditions ({len(conditions)}) in the forall expression')
    assumptions = sort_exprs(assumptions)
    conditions  = sort_exprs(conditions)
    for (a, c) in zip(assumptions, conditions):
        if not equal_expr(a, c):
            raise KurtException(f'EvalError: condition {expr_str(c, kb)} does not match any assumption on the current level')

    # step 3: the remaining body must have been derived
    if len(kb.theory) == 0:
        raise KurtException(f'Nothing was proved in the last local scope')
    last_expr = kb.theory[-1].expr
    if not equal_expr(last_expr, body):
        raise KurtException(f'ProofError: could not prove    {expr_str(body, kb)}\n            instead got        {expr_str(last_expr, kb)}')
    return f'by "forall-intro" (derived from last local scope)'

def not_intro(expr: Expr, kb: KnowledgeBase) -> str:

    # step 0: ensure we are one level up
    if kb.level == 0:
        raise KurtException(f'EvalError: neg-intro requires one level up')
    assert kb.parent is not None
    kb_parent: KnowledgeBase = kb.parent

    # step 1: dissect the `not` expression
    assert isinstance(expr, list)      # must be true, since `expr` is a not-expression
    body = expr[1]

    # step 2: check that `body` was assumed
    assumptions = [f.expr for f in kb.theory if f.proven == False]  # collect all assumptions on the current level
    if len(assumptions) == 1:              # assumptions is one formula
        assumptions = assumptions[0]
    else:                                  # assumptions is a conjunction
        assumptions = simplify([Token(label='SYMBOL', value=AND_SYMBOL)] + assumptions, kb)   # bring to normalform
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

# this function is called when closing a block (via `qed` or 'thus')
def impl_intro(expr: Expr, kb: KnowledgeBase) -> str:
    
    # step 1: collect all assumptions of the current level
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: nothing was shown in the (sub-)proof')
    last_formula = kb.theory[-1]
    premise = [f.expr for f in kb.theory if f.proven == False]
    if not last_formula.proven:
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
            premise = simplify([Token(label='SYMBOL', value=AND_SYMBOL)] + premise, kb)   # bring to normalform
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

# apply substitution to free variables
Subst: TypeAlias = dict[str, Expr]

def apply_subst(expr: Expr, subst: Subst, kb: KnowledgeBase) -> Expr:
    match expr:

        # a token of an (at least locally) free variable, that appears in subst
        case Token(label='SYMBOL', value=free_v) if free_v in subst:
            return subst[free_v]

        # any other token is not modified
        case Token():
            return expr

        # in binding operator expressions the bound variable is not replaced by the substitution
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bound_v), *tail] if isinstance(op, str) and kb.is_bindop(op) and bound_v in subst:
            local_subst: Subst = subst.copy()                   # we need a local `subst`, since `bound_v` should not be changed
            del local_subst[bound_v]                     # remove it from our local copy
            expr2: Expr = apply_subst(expr[2:], local_subst, kb)
            assert isinstance(expr2, list)
            return [expr[0], expr[1], *expr2]

        # recursively replace the children
        case [*children] if len(children) > 0:
            return [apply_subst(child, subst, kb) for child in children]

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
var_counter = 0
def reset_var_counter() -> None:
    global var_counter
    var_counter = 0

def new_var_name() -> str:
    global var_counter
    var_counter += 1
    return f'$$var{var_counter}'   # the `$$` ensures that it is not a valid kurt variable

# new boolean variable names just for internal use
bool_var_counter = 0
def reset_bool_var_counter() -> None:
    global bool_var_counter
    bool_var_counter = 0
def new_bool_var_name() -> str:
    global bool_var_counter
    bool_var_counter += 1
    return f'%%bool{bool_var_counter}'   # the `%%` ensures that it is not a valid kurt variable

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
def rename_all_vars(expr: Expr, subst: Subst, kb: KnowledgeBase, bound_vars: set[str]|None = None) -> tuple[Expr, Subst]:
    # initialize the bound_vars if not given (don't put `set()` as the default value into the signature, since it is only called once and then modified, THIS LEADS TO A VERY SUBTLE BUG)
    if bound_vars is None:
        bound_vars = set()

    # `subst` contains the replacements so far, which are applied also down the AST
    match expr:

        # a token of an (at least) locally free (boolean or not) variable will be replaced either by a known sub or with a new name
        case Token(label='SYMBOL', value=free_v) if isinstance(free_v, str) and (kb.is_var(free_v) or kb.is_bool_var(free_v) or free_v in bound_vars):
            if free_v in subst:
                new_expr = subst[free_v]                 # replace with known substitution
            else:
                if kb.is_var(free_v) or free_v in bound_vars:
                    new_free_v = new_var_name()
                else:
                    new_free_v = new_bool_var_name()
                new_expr = clone_token(expr, new_free_v)   # create a new token by modifying `expr`
                subst[free_v] = new_expr
            return new_expr, subst

        # any other token is not modified
        case Token():
            return expr, subst

        # binding operator expression
        case [Token(label='SYMBOL', value=bind_op),
              Token(label='SYMBOL', value=bind_var), *body] \
              if isinstance(bind_op, str) and kb.is_bindop(bind_op) and isinstance(bind_var, str):

            # operator gets processed with current scope (actually nothing to do)
            head1, subst = rename_all_vars(expr[0], subst, kb, bound_vars)

            # `bind_var` and `body` are processed in the context, that `bind_var in bound_vars`
            new_bound_vars = bound_vars | {bind_var}
            head2, subst = rename_all_vars(expr[1], subst, kb, new_bound_vars)

            # `body` gets new scope including the bound variable
            new_body = []
            for child in body:
                new_child, subst = rename_all_vars(child, subst, kb, new_bound_vars)
                new_body.append(new_child)

            return [head1, head2, *new_body], subst

        # all other expressions
        case [*children] if children:
            new_children = []
            for child in children:
                new_child, subst = rename_all_vars(child, subst, kb, bound_vars)
                new_children.append(new_child)
            return new_children, subst

    assert False, f'BUG: did not match expression `{expr_str(expr, kb)}` in `rename_all_vars`'

def is_sub(expr):
    return isinstance(expr, list) and len(expr)==4 and isinstance(expr[0], Token) and expr[0].label=='SYMBOL' and expr[0].value=='sub'

# check that `expr_a` does not contain freely any variables that are bound at the locations of `token_x` in `expr_A`
# that's quite complicated, so instead we check whether they are among the bound variables of `expr_A`
def bound_var_safe(expr: Expr, token_x: Token, expr_a: Expr|None, expr_A: Expr, kb: KnowledgeBase) -> bool:
    if expr_a is None:
        return True
    else:
        [free_a, _] = free_bound_vars(expr_a, kb)
        [free_A, bound_A] = free_bound_vars(expr_A, kb)
        return free_a.isdisjoint(free_A.union(bound_A))

# INFO: there are two places that can call `yield` several times per function call
# - `generate_all_combinations`
# - binding operator case in `match_exprs`
def generate_all_combinations(expr: Expr, token_x: Token, expr_a: Expr|None, kb: KnowledgeBase) -> Iterator[tuple[Expr|None, Expr]]:
    # generate all `($a, %A)` such that `expr = sub $x $a %A`
    # however, two requirements:
    # (1) `$x` does not appear in `expr` as a free or bound variable, this is ensured by renaming bound variables
    # (2) `$a` does not contain freely any variables that are bound in `%A` (actually only bound at the locations of `$x`)
    [free, bound] = free_bound_vars(expr, kb)
    var_x = token_x.value
    assert var_x not in free and var_x not in bound, f'BUG: `{var_x}` must not appear in `{expr_str(expr, kb)}`'
    for (expr_a, expr_A) in generate_all_combinations_rec(expr, token_x, expr_a):
        if bound_var_safe(expr, token_x, expr_a, expr_A, kb):     # requirement (2)
            yield (expr_a, expr_A)

def generate_all_combinations_rec(expr: Expr, token_x: Token, expr_a: Expr|None, partial: bool=False) -> Iterator[tuple[Expr|None, Expr]]:
    if isinstance(expr, list) and len(expr) == 0:
        yield expr_a, []      # yield once and finish
    else:
        if expr_a is None or equal_expr(expr, expr_a):
            if not partial and not is_sub(expr):
                yield expr, token_x         # $a=expr, $A = $x
        if isinstance(expr, list):
            for (cand_a, cand_A_0) in generate_all_combinations_rec(expr[0], token_x, expr_a):
                for (cand_cand_a, cand_A_tail) in generate_all_combinations_rec(expr[1:], token_x, cand_a, partial=True):
                    assert isinstance(cand_A_tail, list)
                    yield cand_cand_a, [cand_A_0, *cand_A_tail]
        else:
            yield expr_a, expr            # $a=expr_a, $A = expr

def generate_one_combination(expr: Expr, var_x: str, expr_a, expr_A, kb) -> Iterator[tuple[Expr|None, Expr]]:
    cand_expr = apply_subst(expr_A, {var_x: expr_a}, kb)  # substitute `$x` with `expr_a`
    if equal_expr(cand_expr, expr):
        # we have a match, i.e., `expr = sub $x $a $A` where `$a` is `expr_a` and `$A` is `expr_A`
        yield expr_a, expr_A

# couple of problems:
# - also we are generating some wrong combinations where we replace bound variables in `%A` with `$x`, what is allowed, can `$a` contain any bound variables of `%A`?  probably not!
def match_against_sub(expr: Expr, pattern: Expr, tail: list[tuple[Expr, Expr]], subst: Subst, kb: KnowledgeBase) -> Iterator[Subst]:

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
    var_a:  str|None
    a:     Expr|None
    if isinstance(p_a, Token) and isinstance(p_a.value, str) and kb.is_var(p_a.value):
        var_a = p_a.value
        if p_a.value in subst:
            a = subst[var_a]                          # `$a` was already assigned
        else:
            a = None                                  # `$a` is not assigned, we can choose it next
    else:
        var_a = None
        a = p_a                                       # `a` is fixed

    all_combinations: Iterator[tuple[Expr|None, Expr]]  # generator of `a` and `A` that create a match
    var_A: str|None
    if isinstance(p_A, Token) and isinstance(p_A.value, str) and kb.is_bool_var(p_A.value):
        var_A = p_A.value
        if var_A in subst:
            all_combinations = generate_one_combination(expr, var_x, a, subst[var_A], kb)    # `%A` was already assigned earlier
        else:
            all_combinations = generate_all_combinations(expr, token_x, a, kb)
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
            subst_local = subst.copy()
            # we don't have to match `expr` against `expr_A` since `all_combinations` and also `one_combinations` ensure that they match
            if var_A is not None and var_A not in subst_local:
                subst_local[var_A] = expr_A           # store the found substitutions for `%A`
            if var_a is not None and expr_a is not None:
                subst_local[var_a] = expr_a           # store the found substitutions for `$a`
            # now that we found a substitution for `$a` and `%A`, 
            yield from match_exprs(tail, subst_local, kb)

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

def _transform(e: Expr, subst: Subst, kb: KnowledgeBase) -> Expr:
    e_local = deepcopy_expr(e)
    e_local = apply_subst(e_local, subst, kb)
    e_local = trigger_sub(e_local, kb)   # trigger the `sub` operator
    return e_local

# the non-recursive calls are having a single expr and a single pattern, the recursive calls then might have more
# each "case" with a recursive call loops over all generated local substitutions
# `exprs_patterns`:   [(e1, p1), (e2, p2), ...] = zip([e1, e2, ...], [p1, p2, ...])
# this list is necessary for the `[*_]` case, i.e., for matching two lists
def match_exprs(exprs_patterns: list[tuple[Expr, Expr]], subst: Subst, kb: KnowledgeBase) -> Iterator[Subst]:
    debug(f'{exprs_patterns}, subst={subst}')
    match exprs_patterns:

        case []:            # empty list
            yield subst     # we found a substitution

        case [(expr, pattern), *tail]:  # non-empty list
            # in case `expr` is a free variable we can still assign it
            match expr:
                case Token(label='SYMBOL', value=v) if isinstance(v, str) and (kb.is_var(v) or kb.is_bool_var(v)):
                    # `expr` is a free variable, ensure that all expression in the list do the replacement
                    if False:
                        tail_ep = [(_transform(e, {v: pattern}, kb), p) for (e, p) in tail]
                        yield from match_exprs(tail_ep, subst, kb)

            # matches `expr` against `pattern` and extends `subst` (which replaces stuff in `pattern`)
            match pattern:
                # variable matching
                case Token(label='SYMBOL', value=v) if isinstance(v, str) and (kb.is_var(v) or kb.is_bool_var(v) or v in subst):
                    if equal_expr(pattern, expr):
                        # don't extend `subst`, if the variable names are the same
                        yield from match_exprs(tail, subst, kb)
                    elif v not in subst:
                        # `v` is not assigned yet, so we can assign it
                        subst_local: Subst = subst.copy()     # shallow copy
                        subst_local[v] = expr                 # extend the substitution
                        yield from match_exprs(tail, subst_local, kb)
                    elif equal_expr(subst[v], expr):
                        # already assigned to `v`, but the same value
                        yield from match_exprs(tail, subst, kb)
                    else:
                        pass                           # no match possible, since `v` already assigned otherwise

                # symbol matching
                case Token(label=l, value=v):
                    if isinstance(expr, Token) and l==expr.label and v==expr.value:
                        yield from match_exprs(tail, subst, kb)

                # binding operator matching (rename bound variable)
                case [Token(label='SYMBOL', value=op_p), Token(label='SYMBOL', value=v_p), *args_p] if isinstance(op_p, str) and kb.is_bindop(op_p):
                    if op_p == SUB_SYMBOL:
                        # optionally: a pattern with a `sub` is special and possibly matches many expressions
                        if not is_sub(expr):   # however, don't match a `sub` expression to a `sub` pattern to avoid an infinite loop
                            yield from match_against_sub(expr, pattern, tail, subst, kb)
                    # in any case: additionally binding ops match against their matching binding ops
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), Token(label='SYMBOL', value=v_e), *args_e]:
                            if op_p==op_e and len(args_p)==len(args_e):
                                subst_local = subst.copy()
                                assert isinstance(v_p, str)
                                # case 1: v_p == v_e
                                #   block `v_p` from being assigned
                                # case 2: v_p != v_e
                                #   replace `v_p` with `v_e`
                                subst_local[v_p] = expr[1]   # covers both cases!
                                yield from match_exprs(list(zip(args_e, args_p)) + tail, subst_local, kb)

                # list matching for flat and non-symmetric operators (do allow different lengths)
                case [Token(label='SYMBOL', value=op_p), *tail_p] if isinstance(op_p, str) and (kb.is_flat(op_p) and not kb.is_sym(op_p)):
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), *tail_e] if isinstance(op_e, str) and op_e==op_p:
                            if len(tail_e) >= len(tail_p):  # we can assign variables in `tail_p` to elements of `tail_e`
                                splits = split_into_lists(tail_e, len(tail_p))
                                for split in splits:
                                    # convert singletons into elements and add the operator to longer lists
                                    split_expr: list[Expr] = [child[0] if len(child)==1 else [expr[0], *child] for child in split]
                                    yield from match_exprs(list(zip(split_expr, tail_p)) + tail, subst, kb)

                # list matching for non-flat and symmetric operators (do not allow different lengths)
                case [Token(label='SYMBOL', value=op_p), *tail_p] if isinstance(op_p, str) and (not kb.is_flat(op_p) and kb.is_sym(op_p)):
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), *tail_e] if isinstance(op_e, str) and op_e==op_p:
                            if len(tail_e) == len(tail_p):
                                perms = itertools.permutations(tail_e)
                                for perm in perms:
                                    yield from match_exprs(list(zip(perm, tail_p)) + tail, subst, kb)

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
                                        yield from match_exprs(list(zip(perm_expr, tail_p)) + tail, subst, kb)

                # list matching (same length, no special operators)
                case [*_] if isinstance(expr, list) and len(expr)==len(pattern):
                    yield from match_exprs(list(zip(expr, pattern)) + tail, subst, kb)

                case _:
                    # we didn't match the pattern, so we cannot extend the substitution
                    pass

        case _:                                                                                          # pragma: no cover
            # we didn't cover all cases!  bug!  either the outer `match` or the inner one failed
            assert False, f'BUG: not all cases covered'                                                  # pragma: no cover
        
def expr_without_boolean_var(expr: Expr, kb: KnowledgeBase) -> bool:
    # check whether `expr` is a final expression, i.e., it does not contain any boolean variables
    match expr:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_bool_var(v):
            return False  # boolean variable
        case Token():
            return True   # not a boolean variable
        case [*children]:
            return all(expr_without_boolean_var(child, kb) for child in children)

def trigger_sub(expr: Expr, kb: KnowledgeBase) -> Expr:
    # trigger the `sub` operator, i.e., replace `sub $x $a $x=0` with `$x=$a`
    # trigger only if there is no boolean variable in the sub expression
    match expr:
        case [Token(label='SYMBOL', value=v), Token(label='SYMBOL', value=var_x), e_a, e_A] if isinstance(v, str) and v==SUB_SYMBOL:
            if expr_without_boolean_var(e_A, kb):
                assert isinstance(var_x, str)
                return apply_subst(e_A, {var_x: e_a}, kb)  # replace `$x` with `a` in `A`
            else:
                return expr
        case [*children]:
            # recurse
            new_expr = []
            for child in children:
                new_child = trigger_sub(child, kb)
                new_expr.append(new_child)
            return new_expr
        case _:
            return expr      # no sub operator, so we return the original expression

# match the theory against a a list of expressions (not the other way around) and grow the substitution
def match_all_theory(exprs: list[Expr], kb: KnowledgeBase) -> tuple[bool, list[Formula]]:
    debug(f'exprs: [{", ".join([expr_str(e, kb) for e in exprs])}]')
    match exprs:

        # we matched all `exprs`, done!
        case []:
            return True, []
        
        # still at least one to go
        case [expr, *tail]:
            # iterate over all formulas of the theory
            for candidate in kb.all_theory():
                # iterate over all possible substitutions that create a match
                # IMPORTANT: match the candidate to the expression (not vice versa)
                for subst in match_exprs([(candidate.simplified_expr, expr)], {}, kb):
                    # try to match the rest of the expressions (the `tail`), but first apply the subst
                    tail_local = [_transform(e, subst, kb) for e in tail]
                    success, found_formulas = match_all_theory(tail_local, kb)
                    if success:
                        return True, [candidate, *found_formulas]   # match was found!  BINGO!
            # no match so far, however, possibly `expr` is a conjunction that we can split into pieces
            match expr:
                # e.g., (A and B) implies C, then `expr = ['and', A, B]`
                case [Token(label='SYMBOL', value=v), *exprs] if v == AND_SYMBOL:
                    # the only place where we might call `match_all_theory` with a list longer than one
                    return match_all_theory(exprs + tail, kb)  # try to match the conjunction
            # still no match, so we return `None` and an empty list
            return False, []       # could not find a match among the candidate `patterns`

    # we calling `match_all_theory` wrongly, bug!
    assert False, f'BUG: `match_all_theory` did not cover all cases for {exprs}'

# _implies
# checks whether `proven_expr` implies `new_expr`
# we assume that there are no outer universal quantifier
# if the implication is true, then `Subst` constrains the `premise` and puts requirements, 
# a free variable in `premise` could be assigned to a constant or another free variable in `conclusion`
def _implies(proven_expr: Expr, new_expr: Expr, kb) -> Iterator[Subst]:
    yield from match_exprs([(new_expr, proven_expr)], {}, kb)

# what is happening:
# 0. deep copy `proven_formula` and rename all its variables (happens already in the construction of it)
# 1. split `proven_formula` into `conclusion` and `premises`
# 2. match `expr` against `conclusion` (and create a substitution that replaces free variables in conclusion)
# 3. match theory against the `premises` (not the other way around)
def impl_elim(expr: Expr, proven_formula: Formula, kb: KnowledgeBase, filename: str, mainstream: bool) -> str:

    debug(f'{expr_str(expr, kb)} against {expr_str(proven_formula.expr, kb)}')

    # continue with the renamed and simplified variant of `proven_formula` that is generated during the construction of it
    formula_expr: Expr = proven_formula.simplified_expr

    # assign `conclusion` and `premises`
    premise: Expr|None = None
    if is_implication(formula_expr):      # case 1: implication with a premise
        assert isinstance(formula_expr, list)
        conclusion: Expr = formula_expr[2]
        premise          = formula_expr[1]

    else:                                 # case 2: "implication" with an empty premise (think of `true implies $A`)
        conclusion = formula_expr

    # to match `conclusion` and `premise` iterate over all possible substitutions of the `conclusion`
    for subst in _implies(conclusion, expr, kb):
        if premise is None:
            debug('bingo!')
            break           # bingo!  we found one
        else:
            # deep copy of `premise` is necessary, since `match_all_theory` will be called several times with the different substitution `subst`
            # and we have to apply the various substitutions to it, which might change from call to call
            premise_local = deepcopy_expr(premise)
            premise_local = apply_subst(premise_local, subst, kb)
            premise_local = trigger_sub(premise_local, kb)   # trigger the `sub` operator, i.e., replace `sub $x $a $x=0` with `$x=$a`

            # search for the premise as well, i.e., match the theory against the `premise`
            success, matched_formulas = match_all_theory([premise_local], kb)
            if success:
                debug('bingo!')
                break           # bingo!  we found one
    else:
        debug('failed')
        return ''     # no luck this time

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
    return reason    # bingo!  found an implication (and a substitution)

def derive_expr(expr: Expr, kb: KnowledgeBase, filename: str, mainstream: bool) -> list[str]:

    # deep copy `exp` and to a simplifications
    expr = deepcopy_expr(expr)  # deep copy to avoid modifying the original expression
    expr = simplify(expr, kb)   # simplify the expression, e.g., remove redundant

    # "top-intro"
    if isinstance(expr, Token) and expr.label=='SYMBOL' and expr.value==TRUE_SYMBOL:
        return ['by "top-intro"']

    # "impl-elim": iterate over the previously proven formulas that form the current theory
    # this includes restatements
    for proven_formula in kb.all_theory():
        reason = impl_elim(expr, proven_formula, kb, filename, mainstream)
        if len(reason) > 0:
            assert isinstance(reason, str)
            return [reason]

    # if `expr` is a conjunction we can try to derive each of the subexpressions
    match expr:
        case [Token(label='SYMBOL', value=v), *clauses] if v==AND_SYMBOL:
            subst: Subst = {}
            reasons: list[str] = []
            for clause in clauses:
                more_reasons = derive_expr(clause, kb, filename, mainstream)
                if more_reasons is None:
                    break   # failed to derive the next clause
                reasons.extend(more_reasons)
            if len(reasons) > 0:
                return reasons

    # couldn't derive formula using any of the rules
    raise KurtException(f'ProofError: can not derive expression')

def scan_parse_check_eval(input_line: str, kb: KnowledgeBase, line: int, filename: str, mainstream:bool=False) -> KnowledgeBase:
    ts   = PeekableGenerator(scan_string(input_line, kb))                                                   # lexer
    keyword_token, expr, label = parse_tokenstream(ts, kb)       # parser
    kb   = eval_expression(keyword_token, expr, label, kb, line, filename, mainstream) # evaluation
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
            raise KurtException(f'EvalError: can not load library "{fname}" twice, it has already been loaded on level {load_level}')
        with open(fname, encoding='utf-8') as f:
            kb = read_eval_loop(f, kb, markdown, mainstream=mainstream)
    except OSError as e:
        # we have to add `from None` to avoid exception chaining, since we only want to see the KurtException
        raise KurtException(f'EvalError: unable to open "{filename}" searching at {path}') from None
    
    # checks after closing the file
    if kb.level != level:
        kb.level = level       # set levels back before raising the exception
        raise KurtException(f'\nEvalError: inside "{fname}" not all blocks closed, missing "qed"?')
    if len(kb.show) != 0:
        s = '\nNot shown:\n'
        for f in kb.show:
            s += f'    {f.formula_str(kb):<{reason_indent-4}}; {os.path.basename(f.filename)}:{f.line}'
        raise KurtException(f'{s}\n\nEvalError: inside "{fname}" not all promised formulas were proven.')
    kb.libs.append(fname)
    return kb

###########################
## commandline interface ##
###########################

def prompt(level: int, line: int, continued: bool=False) -> str:
    s = '> ' * level
    if continued:
        s += f'...[{line}] '                        # line continuation
    else:
        s += f'!!![{line}] '                        # the bangs mean "show!"
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
                        msg = f'  File "{e.filename}", line {e.line}\n'
                    msg += f'    {input_line}\n'
                    msg += f'    {" " * e.column + "^"}\n'
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
    print('Status:   ' + ('✅ Passed' if result.wasSuccessful() else '❌ Failed'))

def main() -> None:
    print(f'This is Kurt, Version {version} ({made_by})', file=sys.stdout)
    args = parse_args()

    # run tests?
    if args.test:
        print('Running tests...', file=sys.stdout)
        run_tests()
        print('All tests passed.', file=sys.stdout)
        exit(0)

    # debug flag?
    global debug_flag
    debug_flag = args.debug
#    debug_flag = not debug_flag    # swap the debug flag for "run and debug"

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
            kb = load_file(args.filename, kb, mainstream=mainstream)
            if mainstream:
                log('Proof checked.', '', kb.level)
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
