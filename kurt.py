#!/usr/bin/env python3
from __future__ import annotations

## kurt.py
# the kurt programming language for proof writing and checking
# developed by Stefan Harmeling (2016-2025)

## all external libraries (let's keep the dependencies minimal)
import sys          # sys.stdin, sys.stderr
if sys.version_info < (3, 10):
    print("Python 3.10 or newer is required, since we are using Python's `match`!  Sorry about that!", file=sys.stderr)
    exit(0)
import os           # os.path.[isfile, dirname, abspath, join, basename, split, expanduser, exists]
import argparse     # argparse.ArgumentParser
import copy         # copy.deepcopy
import re           # re.[compile, VERBOSE, MULTILINE]
import functools    # functools.cmp_to_key
import readline     # readline.[parse_and_bind, add_history, read_history_file, write_history_file]
import atexit       # atexit.register
import inspect      # inspect.stack

from dataclasses import dataclass
from typing import TypeAlias, Literal, Callable, TypeVar, Generic, Iterator, Pattern, TextIO

# config: general information
version        = 0.1
made_by        = 'made by Stefan Harmeling, 2025'

# config: the indentation for the different blocks
md_indent      = 7                     # ignore all lines not starting with `md_indent` many spaces
proof_indent   = 4                     # how much to indent for a `proof` block
reason_indent  = 60                    # how much the reason is indented

# config: the symbols for the most basic logical operators
impl_symbol    = 'implies'             # symbol for implication
sub_symbol     = 'sub'                 # symbol for substitution
and_symbol     = 'and'                 # symbol for and
eq_symbol      = '='                   # symbol for equality
true_symbol    = 'true'                # symbol for true

# config: the default theory and default path
default_theory: str    = 'theory.kurt'                                                   # default theory
this_file_path: str    = os.path.dirname(os.path.abspath(__file__))                      # path of THIS file
theory_path: list[str] = ['.', 'theories', os.path.join(this_file_path, 'theories')]     # default path for theories

debug_flag = False
def debug(*s) -> None:
    if debug_flag:
        caller = inspect.stack()[1].function
        print(f'DEBUG[{caller}]:', ' '.join(map(str, s)), file=sys.stdout)

## processing a kurt-file does the following steps in a single pass
# level1: lexing
# level2: parsing
# level3: simple type checking
# level4: proving

## links
# https://leanprover-community.github.io/logic_and_proof/natural_deduction_for_first_order_logic.html

### NEXT
# 
# TODO think about all `_local` variables with `.copy` or `.deepcopy`: are they really needed?
# TODO rename variables just with formula creation, store an internal version and a version for viewing
# TODO allow boolean expressions for the bound variable for some variable binding operators
# TODO add type information, add Final for constants, set `Python › Analysis: Type Checking Mode` to `basic`
# TODO allow commandline args for setting builtin keywords, such as `implies` and `and` and `=` and `sub`
# TODO CHECK THE IMPLEMENTATION WHETHER CONSTRAINTS (i) and (ii) for bindop are enforced
# TODO check whether we need a version of `equal_expr` that allows bounded renaming
# TODO check number of possible variable names, use letters to be safe
# TODO `def ($A // $x=$a) = sub $x $a $A` as a macro mechanism, i.e., just syntactically instead of `use`
# TODO check whether we need more deep copy for stuff
# TODO type checking for `sub $x $a $A` with free and bound variable check
# TODO have `origin` (see class Token) also on the Formula level
# TODO macros: `macro ($A // $x=$a) (sub $x $a $A)` expands during parsing
# TODO substitutions are only allowed in `use` lines, not in regular stuff, so they are designed to formulate axiom schemata.
# TODO `parse ( 12, 232 )` and `parse < 12, 32>` generates syntax errors.
# TODO when the matching against substitutions works, check what is the minimal amount of hard-coded rules in python
# TODO get `load-twice.kurt` to run properly
# TODO check that `minimal.kurt` is really hard-coded here
# TODO matching set of formulas: first match the ones without substitutions, then the ones with (can we detect, when it doesn't work?)
# TODO possibly we just need a better `impl_elim` that takes into account equations (i.e., equality of terms), then we don't need `equal-elim`
# TODO do we need `restatement` or can we use it as a special case of `equal-elim`.
# TODO create an initial version and start working on the branch
# TODO have keywords: `free` and `bound`
# TODO maybe it is a good idea to always have variables with $x and constants without them.  However, using `$+` might be cumbersome.  So having the ability to write `var (+)` might be useful.
# TODO next: implement `equal_elim`
# TODO show also the premises in the reasons
# TODO runtime; currently: `derive_expr` is O(n^k) where n is the length of the theory and k is the maximum number of premises of an proved implication, 
#      this could be speed up with better data structure to store the formulas of the theory, but let's first keep it slow, but understandable
# TODO Q: is the match of `match_exprs` always unique?  we are assuming it!
# TODO turn `load_file` into a method of class KnowledgeBase
# TODO allow outer forall block around implications
# TODO put everything into a symbol table?  let's have it additionally.
# TODO write kurt integration for vscode, highlight the lines that are proven, https://microsoft.github.io/language-server-protocol/
# TODO two algorithms: constraint based (https://www.youtube.com/watch?v=H7x4THVU4BQ) and substitution based (W)
# TODO redo something like https://terrytao.wordpress.com/2023/12/05/a-slightly-longer-lean-4-proof-tour/
#                          https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/
# TODO organize the implications as a dictionary of lists with the top-level operator of RHS as the key
# TODO implement 'nonassoc', this could then be checked in 'post_process'
# TODO have a useful exception, if we load a file twice
### LATER/MAYBE
# TODO integration:    `int x in (0, 1)  f(x)
# TODO replace `functool.cmp_to_key` and rewrite `compare_expr`
# TODO LBYL and EAFP Coding Style? <https://realpython.com/python-lbyl-vs-eafp/>
# TODO do multi-line equations and iff, (either using `_` or use indentation for begin/end block
# TODO https://en.wikibooks.org/wiki/Haskell/Indentation#:~:text=The%20golden%20rule%20of%20indentation&text=When%20you%20start%20the%20expression,acceptable%20and%20may%20be%20clearer).&text=This%20tends%20to%20trip%20up,expressions%20must%20be%20exactly%20aligned.
# TODO maybe not: do automatic line continuation if more tokens are required, e.g. after '+'
# TODO format "latex", also allow custom latex formats
# TODO keep the code below 1000 lines of code!  unlikely...
# TODO add back the `formula-flags` from the `formula-flag` branch?  instead use string comments?
# TODO use the Token.column information
# TODO create test code for each possible KurtException

class KurtException(Exception):
    def __init__(self, msg:str, column:int|None=None, line:int|None=None, filename:str|None=None, short:bool=False) -> None:
        self.msg:      str      = msg
        self.column:   int|None = column
        self.line:     int|None = line
        self.filename: str|None = filename
        self.short:    bool     = short

## the syntax is stored in a hierarchical knowledge base called `KnowledgeBase`
format_options: list[Format] = ['sexpr', 'normal']         # sexpr: (+ 1 (* 3 4)), normal: (1 + (3 * 4))
keywords: dict[str, str] = {
    'help':        'print this help',
    'parse':       'parse a string and print its representation',
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
    'var':         'declare symbols as variable, symbols starting with $ are always variables',
    'const':       'declare symbols as constants',
    'alias':       'add some aliases for a symbol',

    'theory':      'print all formulas',
    'equations':   'print all equations',
    'implications':'print all implications',

    # formulas
    'use':         'use a formula without proof as a axiom',
    'assume':      'assume a formula',
    'show':        'plan to prove a formula',
    'proof':       'start a block and open a new level to prove the last planned formula',
    'qed':         'end a block, pop one level and finish the proof of the last planned formula',
    }
keywords_with_parsing: list[str] = ['use', 'assume', 'show']

# types
Label:  TypeAlias = Literal['SYMBOL', 'INT', 'FLOAT', 'STRING', 'END']
Value:  TypeAlias = str | int | float
Format: TypeAlias = Literal['sexpr', 'normal']
Status: TypeAlias = Literal['use', 'assume', 'show'] | None

@dataclass
class Token:
    label: Label
    value: Value
    column: int | None = None
    origin: Value | None = None

    def __repr__(self) -> str:
        return f'({self.label} "{self.value}")'

    def __lt__(self, other: Token) -> bool:
        return str(self.value) < str(other.value)   # note: this is not a good ordering on integers

class Formula:
    next_id: int = 0
    def __init__(self, expr:Expr, line:int, filename:str, status:Status, reason:str|None=None, comment:str|None=None):
        self.expr: Expr           = expr               # expression of the formula
        self.line: int            = line               # line of this formula
        self.filename: str        = filename           # file of this formula
        self.status: Status       = status             # one of 'use', 'assume', 'show', None (for derived)
        self.reason: str | None   = reason             # the reason why it is true
        self.comment: str | None  = comment            # basically, a label of the formula
        self.id: int              = Formula.next_id    # a unique id for every formula
        Formula.next_id += 1

    def prefix_str(self) -> str:
        s: str = ''
        if self.status is not None:
            s += f'{self.status} '
        return s
    
    def comment_str(self) -> str:
        if self.comment is None:
            return ''
        else:
            return f' "{self.comment}"'
    
    def __str__(self) -> str:
        return f'{self.prefix_str()}{self.expr}{self.comment_str()}'

    def formula_str(self, kb: KnowledgeBase) -> str:
        return f'{self.prefix_str()}{expr_str(self.expr, kb)}'

# expression
# not a class itself, instead just a type alias
Expr: TypeAlias = list["Expr"] | Token

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


# hierarchical knowledge base
# the level is increased inside blocks and files
# dropping a level drops also all local definitions
Nud: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Token], Expr]
Led: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Expr, Token], Expr]

class KnowledgeBase:
    def __init__(self, parent:KnowledgeBase|None=None, verbose:bool=False) -> None:
        # general
        self.parent: KnowledgeBase|None = parent
        self.level: int            = 0 if parent is None else parent.level + 1
        self.libs: list[str]       = []        # the filenames of loaded libraries

        # syntax
        self.infix:    dict[str, tuple[int,int]] = {}     # left and right binding powers of infix operators
        self.postfix:  dict[str, int]            = {}     # left binding power of postfix operator
        self.prefix:   dict[str, int]            = {}     # right binding power of prefix operator
        self.brackets: dict[str, str]            = {}     # keys are right brackets, values are left brackets
        self.arity:    dict[str, int]            = {}     # for non-zero arities
        self.bindop:   set[str]                  = set()  # for variable binding operators
        self.flat:     set[str]                  = set()  # for declaring a flat operator, i.e. ($a + $b) + $c = $a + $b + $c
        self.sym:      set[str]                  = set()  # for declaring a symmetric operator, i.e. $a + $b = $b + $a
        self.lbp:      dict[str, int]            = {}     # left binding power
        self.rbp:      dict[str, int]            = {}     # right binding power
        self.bool:     dict[str, list[int]]      = {}     # dict of symbols declared to have boolean output
        self.var:      set[str]                  = set()  # dict of variables with unused values
        self.const:    set[str]                  = set()  # dict of constants with unused values
        self.alias:    dict[str, str]            = {}     # dict of alias pointing to the original
        self.nud:      dict[str, Nud]            = {}     # null denotation, entries are functions for parsing expressions
        self.led:      dict[str, Led]            = {}     # left denotation, entries are functions for parsing infix expressions

        # theory
        self.theory: list[Formula] = []        # list of formulas (axioms added by 'use', 
                                               #                   assumptions added by 'assume',
                                               #                   and derived formulas)
        self.show:   list[Formula] = []        # lists of formulas to show

        # misc
        self.format: Format = format_options[1] if parent is None else parent.format  # how formulas look in the shell
        self.verbose: bool  = verbose if parent is None else parent.verbose           # extra information or not

    def entry_str(self, keyword:str, key:str, value:str|int|tuple[int,int]|list[int]|None = None) -> str:
        if   keyword == 'prefix':   return f'prefix "{key}" {value}'
        elif keyword == 'infix':    
            if isinstance(value, tuple) and len(value) == 2:
                return f'infix "{key}" {value[0]} {value[1]}'
            assert False, f'BUG!  Unexpected value for `infix`, got {value}'
        elif keyword == 'postfix':  return f'postfix "{key}" {value}'
        elif keyword == 'brackets': return f'brackets "{value}" "{key}"'
        elif keyword == 'arity':    return f'arity "{key}" {value}'
        elif keyword == 'flat':     return f'flat "{key}"'
        elif keyword == 'sym':      return f'sym "{key}"'
        elif keyword == 'bindop':   return f'bindop "{key}"'
        elif keyword == 'bool':     
            if isinstance(value, list):
                return f'bool "{key}" {' '.join(map(str, value))}'
            assert False, f'BUG!  Unexpected value for `bool`, got {value}'
        elif keyword == 'var':      return f'var "{key}"'
        elif keyword == 'const':    return f'const "{key}"'
        elif keyword == 'alias':    return f'alias "{key}" "{value}"'
        else: assert False, f'BUG: unknown keyword, got {keyword}'

    def dict_or_set_str(self, some_dict_or_set: dict[str,str]|dict[str,int]|dict[str,tuple[int,int]]|dict[str,list[int]]|set[str], keyword: str) -> str:
        if isinstance(some_dict_or_set, dict):
            return '\n'.join([self.entry_str(keyword, key, some_dict_or_set[key]) for key in some_dict_or_set])
        else:
            return '\n'.join([self.entry_str(keyword, key) for key in some_dict_or_set])

    # SYNTAX RELATED
    def syntax_str(self) -> str:
        s: str = self.parent.syntax_str() if self.parent is not None else ''
        s += f'; syntax: declarations on level {self.level}\n'
        s += self.dict_or_set_str(self.prefix,   'prefix')
        s += self.dict_or_set_str(self.infix,    'infix')
        s += self.dict_or_set_str(self.postfix,  'postfix')
        s += self.dict_or_set_str(self.arity,    'arity')
        s += self.dict_or_set_str(self.bindop,   'bindop')
        s += self.dict_or_set_str(self.brackets, 'brackets')
        s += self.dict_or_set_str(self.flat,     'flat')
        s += self.dict_or_set_str(self.sym,      'sym')
        s += self.dict_or_set_str(self.bool,     'bool')
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
        return s in self.var     or (self.parent is not None and self.parent.is_var(s)) or s[0]=='$'   # constant vs variable symbols (variables start with '$')
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

    def is_bracket(self, s: str) -> bool:
        return s in self.brackets.values() or s in self.brackets.keys() or (self.parent is not None and self.parent.is_bracket(s))

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
        self.add_const(fun)
        self.arity[fun] = a

    def find_symbol(self, op: str) -> str:
        if self.is_prefix(op):    return 'prefix'
        elif self.is_infix(op):   return 'infix'
        elif self.is_postfix(op): return 'postfix'
        elif self.is_bracket(op): return 'bracket'
        else: assert False, f'BUG: call "find_symbol" only for existing symbols'

    def add_prefix(self, op: str, rbp: int) -> None:
        if self.is_operator(op) and not self.is_infix(op):    # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self.find_symbol(op)}')
        self.add_const(op)
        self.prefix[op] = rbp
        self.nud[op] = lambda ts, kb, op_token: [op_token, parse_expression(ts, kb, rbp)]

    def add_infix(self, op: str, lbp: int, rbp: int) -> None:
        if self.is_operator(op) and not self.is_prefix(op):   # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self.find_symbol(op)}')
        self.add_const(op)
        self.infix[op] = (lbp, rbp)                           # to nicely list all operators
        self.led[op] = lambda ts, kb, left, op_token: [op_token, left, parse_expression(ts, kb, rbp)]
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_postfix(self, op: str, lbp: int) -> None:
        if self.is_operator(op):
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self.find_symbol(op)}')
        self.add_const(op)
        self.postfix[op] = lbp                                # to nicely list all operators
        def led(_ts: PeekableGenerator, _kb: KnowledgeBase, left: Expr, op_token: Token) -> Expr:
            return [op_token, left]
        self.led[op] = led
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

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
        if self.is_operator(lbracket):
            raise KurtException(f'EvalError: symbol "{lbracket}" already exist as {self.find_symbol(lbracket)}')
        if self.is_operator(rbracket):
            raise KurtException(f'EvalError: symbol "{rbracket}" already exist as {self.find_symbol(rbracket)}')
        self.add_const(lbracket)
        self.add_const(rbracket)
        self.brackets[rbracket] = lbracket    # to list the brackets (not used for parsing)
        def nud(ts: PeekableGenerator, kb: KnowledgeBase, t: Token) -> Expr:
            expr: Expr = parse_expression(ts, kb, 0)
            token: Token = next(ts)
            if token.value != rbracket: 
                raise KurtException(f'SyntaxError: expected "{rbracket}"', column=token.column)
            token.value = f'{lbracket} {rbracket}'    # use a value that can not come from the tokenizer
            return [token, expr]
        self.nud[lbracket] = nud
        self.lbp[rbracket] = bracket_lbp

    def add_var(self, s: str) -> None:
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a constant')
        self.var.add(s)

    def add_const(self, s: str) -> None:
        if self.is_var(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a variable or starts with $')
        self.const.add(s)

    def add_alias(self, s: str, t: str) -> None:
        if self.is_var(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a variable or starts with $')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a constant')
        if not (self.is_var(t) or self.is_const(t)):
            raise KurtException(f'EvalError: symbol "{t}" must be either a variable or a constant')
        self.alias[s] = t         # add a key `s` with value `t`

    def add_bool(self, s: str, v: list[int]) -> None:
        if len(self.bool_sig(s)) > 0:
            raise KurtException(f'EvalError: symbol "{s}" is already declared bool')
        if not (self.is_const(s) or self.is_var(s)):
            self.add_const(s)     # create a constant automatically
        if self.is_bindop(s) and 1 in v:
            raise KurtException(f'EvalError: the first position of binding operators can not be declared boolean')
        self.bool[s] = v          # add a key with value the tuple of positions that are bool

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
            raise KurtException(f'SyntaxError: expression expected, got end of line')
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
            yield f
        if self.parent is not None:
            yield from self.parent.all_theory()

    def all_theory_expressions(self) -> Iterator[Expr]:
        for f in self.all_theory():
            yield f.expr

    def theory_str(self, keyword:str|None=None, op:str|None=None) -> str:
        s: str = self.parent.theory_str(keyword, op) if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.theory:
            if (keyword is None and op is None) or (keyword==f.status):
                s += f'{f.formula_str(self)}\n'
            elif op is not None and is_op_expr(f.expr, op):
                s += f'{f.formula_str(self)}\n'
        return s

    def show_str(self) -> str:
        s: str = self.parent.show_str() if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.show:
            s += f'{f.formula_str(self)}\n'
        return s

# some important constants for the parser
bracket_lbp: int = 0                               # left binding power of brackets
end_lbp:     int = 0                               # left binding power of end of input line
string_lbp:  int = 1                               # left binding power of strings
space_op:    str = ' '                             # must be something that is never returned from the tokenizer
space_lbp:   int = 22                              # left binding power: stronger than eq_symbol
space_rbp:   int = 22                              # right binding power: stronger than eq_symbol

# create initial knowledge base
initial_kb: KnowledgeBase = KnowledgeBase()
initial_kb.add_infix(space_op, space_lbp, space_rbp)   # the space operator is for expression like `f x`
initial_kb.add_infix("//", 3, 3)                       # substitution of variables
initial_kb.add_infix(',', 5, 5)                        # comma with binding power 1
initial_kb.add_infix(impl_symbol, 13, 12)              # implies
initial_kb.add_infix(and_symbol, 16, 16)               # and
initial_kb.add_infix(eq_symbol, 20, 20)                # equality with lower binding power than space, equality is left-associative
initial_kb.add_bool(eq_symbol, [0])                    # equalities are true or false, but the inputs can be anything
initial_kb.add_bool(true_symbol, [0])
initial_kb.add_bool(impl_symbol, [0, 1, 2])
initial_kb.add_bool(and_symbol, [0, 1, 2])
initial_kb.add_flat(',')                               # flatness of comma operator
initial_kb.add_flat('and')                             # flatness of and
initial_kb.add_brackets('(', ')')                      # round brackets for grouping

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
        case None:
            return ''
    assert False, f'BUG: unknown expression, got {expr}'

def expr_normal(expr: Expr, kb: KnowledgeBase, rbp: int=0) -> str:          # create raw input expression
    match expr:
        case Token():
            return expr_sexpr(expr)            # reuse implementation from expr_sexpr
        case [e0]:
            return expr_normal(e0, kb)
        case [Token(label='SYMBOL', value=a), e1] if isinstance(a, str) and kb.is_prefix(a):
            return f'({a} {expr_normal(e1, kb)})'
        case [Token(label='SYMBOL', value=a), e1] if isinstance(a, str) and kb.is_postfix(a):
            return f'({expr_normal(e1, kb)} {a})'
        case [e0, e1]:
            return f'{expr_normal(e0, kb)} {expr_normal(e1, kb)}'
        case [Token(label='SYMBOL', value=a), e1, e2] if isinstance(a, str) and kb.is_infix(a):
            return f'({expr_normal(e1, kb)} {a} {expr_normal(e2, kb)})'
        case [Token(label='SYMBOL', value=a), e1, e2]:
            return f'({a} {expr_normal(e1, kb)} {expr_normal(e2, kb)})'
        case [Token(label='SYMBOL', value=a), *tail] if isinstance(a, str) and kb.is_flat(a):
            return f'({f' {a} '.join([expr_normal(e, kb) for e in tail])})'
        case [*tail]:
            return f'({" ".join([expr_normal(e, kb) for e in tail])})'
        case None:
            return ''
    assert False, f'BUG: unknown expression, got {expr}'

def is_op_expr(e: Expr, op: str) -> bool:
    match e:
        case [Token(label='SYMBOL', value=v), *_]:
            return v == op
        case _:
            return False

def is_equation(expr: Expr) -> bool:
    return is_op_expr(expr, eq_symbol)

def is_implication(expr: Expr) -> bool:
    return is_op_expr(expr, impl_symbol)

def equal_expr(t1: Expr, t2: Expr) -> bool:                               # equality for expressions
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

def simplify(expr: Expr, kb: KnowledgeBase) -> Expr:
    if expr is None:
        return None
    for op in kb.flat:
        expr = flatten_op(op, expr)       # flatten certain operators
    expr = sort_symmetric_ops(kb, expr)   # sort expressions of symmetric operators from the inside to the outside
    return expr

# special tokens that are made for the parser and sometimes artificially generated
space_token: Token = Token('SYMBOL', ' ')      # for expressions like 'f x'
end_token:   Token = Token('END', '')          # for the end of a string

# scanner based on regular expressions (let's support unicode!)
# note that the ordering of the expressions here is important
scanner: Pattern[str] = re.compile(r'''
  (?P<COMMENT> [;].*$)                      | # comments, e.g. ; this is a comment
  (?P<FLOAT>   [0-9]+\.[0-9]+)              | # floating point literals, e.g. 3.14
  (?P<INT> [0-9]+)                          | # integer literals, e.g. 17
  (?P<STRING>  ["][^"]*["])                 | # string literals
  (?P<SYMBOL>  [$]*[^\W\d]\w*               | # symbols 1: identifiers and alphanumeric symbols, they never start with a digit
               [()]                         | # symbols 2: round brackets for grouping
               [,]                          | # symbols 3: comma for lists
               [:=+\-*/.#&^%'@∈!<>{}[\]_]+) | # symbols 4: non-alphanumeric operator symbols, e.g. ++
  (?P<NEWLINE> [\n])                        | # newline, just for getting the line right
  (?P<WHITE>   [^\S\n\r]+)                  | # white space but not newline and colleagues (otherwise the line counting is not right)
  (?P<ERROR>   .)                             # anything else is a scanning error, are there any?
''', re.VERBOSE | re.MULTILINE)
# common white space:
# \t tab
# \n newline
# \r carriage return
# \f form feed
# \v vertical tab

def scan_string(input_line: str) -> Iterator[Token]:

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
            yield Token(label, value, column + len(value))
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

# by replacing aliases as early as possible, we don't have to register the alias as infix, etc
# we store the `origin` for string output
def replace_alias(kb: KnowledgeBase, token: Token) -> Token:
    if token.label == 'SYMBOL':
        assert isinstance(token.value, str)
        t = kb.get_alias(token.value)
        if t is not None:
            token.origin = token.value             # store for string generation
            token.value = t
    return token

# the heart of the Pratt parser (calls 'led' and 'nud' implemented elsewhere in this file)
def parse_expression(ts: PeekableGenerator, kb: KnowledgeBase, rbp: int) -> Expr:
    t: Token = next(ts)                           # get next token
    t: Token = replace_alias(kb, t)               # replace alias
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

def sort_symmetric_ops(kb: KnowledgeBase, expr: Expr) -> Expr:                        # symmetric operators can sort their args
    if isinstance(expr, list):
        expr = [sort_symmetric_ops(kb, e) for e in expr] # start inside
        if isinstance(expr[0], Token) and expr[0].label == 'SYMBOL' and expr[0].value in kb.sym:
            expr = [expr[0]] + sorted(expr[1:], key=functools.cmp_to_key(compare_expr))
        return expr
    elif isinstance(expr, Token):
        return expr
    else:
        assert False, f'BUG: expression must be list or Token, got {expr}'

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
    assert False, f'BUG: expression must be list or Token, got {expr}'

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
    # we assume that `flatten_op` for `op=' '` has been called just before
    # calls `group_by_arity` for each ' ' operator
    match expr:
        case Token():
            return expr
        case [Token(label='SYMBOL', value=' '), *tail]:
            expr, tail = group_by_arity(tail, kb)
            if len(tail) > 0:
                expr = [expr] + tail         # extra arguments (might be there for keywords!)
    assert isinstance(expr, list)
    return [process_arity(e, kb) for e in expr]

def remove_round_brackets(expr: Expr) -> Expr:
    if isinstance(expr, Token):
        return expr
    elif isinstance(expr, list):
        if is_op_expr(expr, '( )'):
            return remove_round_brackets(expr[1])
        else:
            return [remove_round_brackets(e) for e in expr]
    else:
        assert False, f'BUG: list or Token expected, got {expr}'

def check_no_keyword(expr: Expr) -> None:
    match expr:
        case Token(label='SYMBOL', value=v) if v in keywords:
            raise KurtException(f'SyntaxError: keywords not allowed inside expressions', expr.column)
        case [*_]:
            for e in expr:
                check_no_keyword(e)
        case _:
            pass

def check_expr_comment(expr: Expr, kb) -> tuple[Expr, str|None]:            # check [expr] [comment]
    # cases:
    #   x=9  "eq 1"
    #   true
    #   x=9
    comment = None
    match expr:
        case [Token(label='STRING', value=comment), *tail]:  # comments are parsed like very low binding postfix operators
            assert isinstance(comment, str)
            if len(tail) == 1:
                tail = tail[0]
        case [*tail]:
            if len(tail) == 1:
                tail = tail[0]
        case Token():
            tail = expr
        case _:
            assert False, f'BUG: list or Token expected, got {expr}'
    check_no_keyword(tail)             # don't check the `keyword` and the `comment`
    return tail, comment

def post_process(kb: KnowledgeBase, expr: Expr) -> tuple[Expr, str|None]:
    expr = flatten_op(' ', expr)                           # flatten all space operators
    expr = process_arity(expr, kb)                         # turns space operators into function calls according to arities
    expr = remove_round_brackets(expr)                     # remove round brackets for grouping
    expr, comment = check_expr_comment(expr, kb)           # check and split `expr` and `comment`
    expr = simplify(expr, kb)                              # simplify the formula using flatness and symmetry
    return expr, comment

def parse_tokenstream(ts: PeekableGenerator, kb: KnowledgeBase) -> tuple[Token|None, Expr, str|None]:                             # gets a peekable token stream
    assert isinstance(ts.peek, Token)
    keyword_token: Token | None
    if ts.peek.label == 'SYMBOL' and ts.peek.value in keywords:
        keyword_token = next(ts)                           # remove a keyword right away early
    else:
        keyword_token = None
    if ts.peek.label == 'END': 
        return keyword_token, [], None                     # empty token stream
    if keyword_token is None or keyword_token.value in keywords_with_parsing:
        expr: Expr
        comment: str|None
        expr          = parse_expression(ts, kb, 0)        # parse expression
        expr, comment = post_process(kb, expr)             # turn spaces into calls, symmetry, flatness
        type_check_expression(expr, kb)                    # (some) type checking
    else:
        expr = list(ts)[:-1]                               # [:-1] removes end_token
        comment = None
    return keyword_token, expr, comment

## kurt eval
def create_usage(keyword: str, arg_labels: list[list[Label]]) -> str:
    s: str = ''
    for arg_label in arg_labels:
        s += f'    {keyword}'
        for l in arg_label:
            s += f' {l}'
        s += f'\n'
    return s

# def check_args(keyword_token: Token, expr: Expr, arg_labels: list[list[Label]]) -> None:
#     # e.g. 'check_args(keyword_token, expr, [[], ['SYMBOL', 'INT']], ['list', 'add'])
#     # where [] implies none is possible
#     # where ['SYMBOL', 'INT'] implies two args with symbol and integer are possible as well
#     msg = create_usage(str(keyword_token.value), arg_labels)
#     for arg_label in arg_labels:
#         assert isinstance(expr, list)
#         if len(expr) == len(arg_label):
#             for (e, l) in zip(expr, arg_label):
#                 if l != 'EXPR':                    # expressions are fine as they are
#                     if not isinstance(e, Token) or e.label != l:
#                         raise KurtException(f'EvalError: wrong argument types, possible is:\n{msg}')
#             return       # we found a correct number of arguments and checked all labels
#     if ['EXPR'] not in arg_labels:
#         raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)

def strip_keyword(s: str, column: int) -> str:
    return s[(1+column):]                  # get rid of the keyword at the beginning

def decorate_reason(mainstream: bool, reason: str, filename: str, line: int) -> str:
    if mainstream:
        return f'{line} {reason}'
    else:
        return f'{os.path.basename(filename)}:{line} {reason}'

def eval_keyword_expression(keyword_token: Token, args: Expr, comment: str|None, kb: KnowledgeBase, line: int, filename: str, mainstream: bool) -> KnowledgeBase:
    keyword = keyword_token.value
    assert isinstance(keyword, str)

    # GENERAL STUFF
    if keyword == 'help':
        match args:
            case []:
                for k in keywords.keys(): print(f'  {k:<12} {keywords[k]}', file=sys.stdout)
            case _:
                raise KurtException(f'ParseError: "{keyword}" does not take arguments', keyword_token.column)
    elif keyword == 'load':
        current_path: str = os.path.split(filename)[0]    # search first at the current path
        match args:
            case [Token(label='STRING', value=fname)]:
                assert isinstance(fname, str)
                kb = load_file(fname, kb, path=[current_path]+theory_path, mainstream=False)[0]
            case _:
                raise KurtException(f'ParseError: "{keyword}" takes a string for the filename', keyword_token.column)
    elif keyword == 'parse':
        match args:
            case []:
                msg: str = ''
            case [*expr_list]:
                tokenlist: Expr = expr_list + [end_token]           # add end token for parse_expression
                ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))               # turn list into peekable generator
                expr = parse_expression(ts, kb, 0)            # parse the tokenlist
                expr, comment = post_process(kb, expr)        # turn spaces into calls, symmetry, flatness
                msg = f'{expr_str(expr, kb)}'
                if comment is not None:
                    msg += f' "{comment}"'
            case _:
                assert f'BUG: `args` must be a list'
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
        match args:
            case []:
                print(kb.level, file=sys.stdout)
            case _:
                raise KurtException(f'ParseError: "{keyword}" does not take any arguments', keyword_token.column)

    # SYNTAX RELATED
    elif keyword == 'syntax':
        match args:
            case []:
                print(kb.syntax_str(), file=sys.stdout)
            case _:
                raise KurtException(f'ParseError: "{keyword}" does not take any arguments', keyword_token.column)
    elif keyword == 'prefix':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.prefix, keyword), file=sys.stdout)
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
                print(kb.dict_or_set_str(kb.postfix, keyword), file=sys.stdout)
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
                print(kb.dict_or_set_str(kb.infix, keyword), file=sys.stdout)
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
                print(kb.dict_or_set_str(kb.arity, keyword), file=sys.stdout)
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
                print(kb.dict_or_set_str(kb.brackets, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=lbracket), Token(label='STRING'|'SYMBOL', value=rbracket)]:
                kb.add_brackets(lbracket, rbracket)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'bindop':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.bindop, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_bindop(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'flat':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.flat, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_flat(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'sym':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.sym, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                kb.add_sym(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'bool':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.bool, keyword), file=sys.stdout)
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
                print(kb.dict_or_set_str(kb.var, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_var(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'const':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.const, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=op)]:
                assert isinstance(op, str)
                kb.add_const(op)
            case _:
                msg = create_usage(keyword, [[], ['STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'alias':
        match args:
            case []:
                print(kb.dict_or_set_str(kb.alias, keyword), file=sys.stdout)
            case [Token(label='STRING'|'SYMBOL', value=s), Token(label='STRING'|'SYMBOL', value=t)]:
                assert isinstance(s, str) and isinstance(t, str)
                kb.add_alias(s, t)
            case _:
                msg = create_usage(keyword, [[], ['STRING', 'STRING']])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)

    # THEORY AND PROOF RELATED
    elif keyword == 'theory':
        match args:
            case []:
                print(kb.theory_str(), file=sys.stdout)
            case _:
                msg = create_usage(keyword, [[]])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == "equations":
        match args:
            case []:
                print(kb.theory_str(op=eq_symbol), file=sys.stdout)
            case _:
                msg = create_usage(keyword, [[]])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == "implications":
        match args:
            case []:
                print(kb.theory_str(op=impl_symbol), file=sys.stdout)
            case _:
                msg = create_usage(keyword, [[]])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword in ['use', 'assume']:
        match args:
            case []:
                print(kb.theory_str(keyword=keyword), file=sys.stdout)
            case [expr] | [*expr]:
                reason = {'use': 'axiom', 'assume': 'assumption'}[keyword]
                if comment is not None:
                    reason += f' {comment}'
                if not bool_expr(expr, kb):
                    raise KurtException(f'EvalError: must evaluate to boolean')
                assert keyword in ('use', 'assume')
                f = Formula(expr, line, filename, status=keyword, reason=reason, comment=comment)
                kb.theory.append(f)
                if mainstream:
                    reason = decorate_reason(mainstream, reason, filename, line)
                    log(f.formula_str(kb), reason , kb)
            case _:
                assert f'BUG: `args` must be a list'
    elif keyword in ['show']:
        match args:
            case []:
                print(kb.show_str(), file=sys.stdout)
            case [expr] | [*expr]:
                if not bool_expr(expr, kb):
                    raise KurtException(f'EvalError: must evaluate to boolean')
                f = Formula(expr, line, filename, status='show', comment=comment)  # syntactic sugar for theorem, proposition, lemma
                kb.show.append(f)
                if mainstream:
                    reason = decorate_reason(mainstream, 'claim', filename, line)
                    if comment is not None:
                        reason += f' {comment}'
                    log(f.formula_str(kb), reason , kb)

            case _:
                assert f'BUG: `args` must be a list'
    elif keyword == 'proof':                  # opens a new block (scope)
        match args:
            case []:
                if len(kb.show) == 0:
                    raise KurtException(f'ProofError: can not start proof since there is no planned formula on current level')
                if mainstream:
                    log('proof', None, kb)
                kb = KnowledgeBase(kb)                # add a new level/scope to the knowledgebase
            case _:
                msg = create_usage(keyword, [[]])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    elif keyword == 'qed':                    # closes the last block (scope)
        match args:
            case []:
                if kb.level == 0:
                    raise KurtException(f'EvalError: no block to close')
                if len(kb.show) > 0:                  # any planned formulas inside the current proof?
                    pf = kb.show[-1]
                    raise KurtException(f'ProofError: planned formula "{pf}" in current proof is unproven')
                assert kb.parent is not None, f'BUG: we should be one level up'
                assert len(kb.parent.show) > 0, f'BUG: no planned formula on previous level, this should have been already checked when calling "proof"'
                pf = kb.parent.show[-1]               # peek at the last planned formula from previous level
                reason = impl_intro(pf.expr, kb)      # this might generate a KurtException
                kb = kb.parent                        # drop current level
                f = Formula(pf.expr, line, filename, status=None, reason=reason)
                kb.show.pop()                         # pop it now off the show stack, since it was proved
                kb.theory.append(f)                   # add a copy to the theory
                if mainstream:
                    log('qed', None, kb)
                    reason = decorate_reason(mainstream, reason, filename, line)
                    log(f.formula_str(kb), reason, kb)
            case _:
                msg = create_usage(keyword, [[]])
                raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
    else:
        assert False, f'BUG: unknown keyword, got "{keyword}"'

    # finally return the possibly modified knowledgebase
    return kb

def eval_expression(keyword_token: Token|None, expr: Expr, comment: str|None, kb: KnowledgeBase, line: int, filename: str, mainstream: bool) -> KnowledgeBase:
    if keyword_token is None:
        # expression without keyword: try to derive the formula and add it to the theory
        if expr==[]:
            return kb
        if not bool_expr(expr, kb):
            raise KurtException(f'EvalError: must evaluate to boolean')
        reason = derive_expr(expr, kb, filename, mainstream)  # this might raise ProofError exceptions
        f = Formula(expr, line, filename, status=None, reason=reason)
        kb.theory.append(f)                         # add it to the knowledge base
        if mainstream:
            reason = decorate_reason(mainstream, reason, filename, line)
            log(f.formula_str(kb), reason, kb)
        return kb
    else:
        # iterate over the expr to allow ',' in keyword expressions
        args = []
        if not isinstance(expr, list):
            expr = [expr]
        for e in expr:
            match e:
                case Token(label='SYMBOL', value=','):
                    if len(args) == 0:
                        raise KurtException(f'ParseError: nothing to separate with a comma, comma can not be used with `use`, `assume`, `show`, etc.')
                    kb = eval_keyword_expression(keyword_token, args, comment, kb, line, filename, mainstream)
                    args = []
                case _:
                    args += [e]
        kb = eval_keyword_expression(keyword_token, args, comment, kb, line, filename, mainstream)
        return kb

########################
## kurt type checking ##
########################

def bool_expr(expr: Expr, kb: KnowledgeBase) -> bool:
    match expr:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
            return True                    # variables are potentially boolean
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and not kb.is_var(v):
            return 0 in kb.bool_sig(v)
        case [Token(label='SYMBOL', value='//'), *tail]:
            return bool_expr(tail[0], kb)
        case [Token(label='SYMBOL', value=v), *_] if isinstance(v, str) and not kb.is_var(v):
            return 0 in kb.bool_sig(v)
    return False

def type_check_expression(expr: Expr, kb: KnowledgeBase) -> None:
    # this is for now hardcoded, should be part of the syntax definitions
    match expr:
        # binding operators such as `forall`, `exists`, `lim`, `int`
        case [Token(label='SYMBOL', value=op), *tail] if isinstance(op, str) and kb.is_bindop(op):
            if len(tail) < 2:
                raise KurtException(f'TypeError: arity of binding operator must be at least two')
            if 1 in kb.bool_sig(op):
                assert False, f'BUG: there should not be `1` in kb.bool for binding operators'
            for idx in range(2, len(tail)+1):
                if idx in kb.bool_sig(op) and not bool_expr(tail[idx-1], kb):
                    raise KurtException(f'TypeError: arg {idx} of `{expr}` must be boolean')
            match tail[0]:
                case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
                    pass
                case [*cond]:
                    if not bool_expr(cond, kb):
                        raise KurtException(f'TypeError: first arg of binding operator must be variable or boolean, got {cond}')
                    # check existence of a free variable
                    fv: set[str] = free_bound_vars(cond, kb)[0]
                    if len(fv) == 0:
                        raise KurtException(f'TypeError: first arg must be or must contain at least one free variable')
                case _:
                    assert False, f'BUG: did not match {tail[0]} while type checking'
            # recursive calls
            for e in tail:
                type_check_expression(e, kb)
        # arity > 0: prefix, postfix, infix, ...
        case [Token(label='SYMBOL', value=op), *tail]:
            for idx in range(1, len(tail)+1):
                if isinstance(op, str) and idx in kb.bool_sig(op) and not bool_expr(tail[idx-1], kb):
                    raise KurtException(f'TypeError: arg {idx} of `{expr}` must be boolean, but is  `{tail[idx-1]}`')
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

def log(s: str, reason: str|None, kb: KnowledgeBase) -> None:
        indent: str = ' ' * (proof_indent * kb.level)
        if reason is None:
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

# this function is called when closing a block (via `qed` or using indentation)
def impl_intro(expr: Expr, kb: KnowledgeBase) -> str:
    
    # step 1: collect all assumptions of the current level
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: nothing was shown in the (sub-)proof')
    last_formula = kb.theory[-1]
    premise = [f.expr for f in kb.theory if f.status=='assume']
    if last_formula.status != None:
        raise KurtException(f'ProofError: last formula in a (sub-)proof can not have `show`, `assume`, `use` status')
    conclusion = last_formula.expr        # last element is the conclusion

    # step 2: form a formula using the last formula in the current level
    reason = 'by impl-intro (derived from last proof)'
    if len(premise) == 0:                  # just the conclusion (empty premise)
        result = conclusion
        reason = 'by last proof'
    else:
        if len(premise) == 1:              # premise is one formula
            premise = premise[0]
        else:                              # premise is a conjunction
            premise = simplify([Token(label='SYMBOL', value=and_symbol)] + premise, kb)   # bring to normalform
        result = [Token(label='SYMBOL', value=impl_symbol), premise, conclusion]       # construct implication

    # step 3: compare against the planned expression `expr`
    if equal_expr(expr, result):
        if kb.verbose:
            print(f'goal    {expr}', file=sys.stdout)
            print(f'derived {result}', file=sys.stdout)
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

    assert False, f'BUG: did not match expression `{expr}` in `apply_subst`'

# note that a variable can be free and bound at the same time in an expression
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
        
    assert False, f'BUG: did not match expression `{expr}` in `free_bound_vars`'

# new variable names just for internal use
var_counter = 0
def reset_var_name_counter() -> None:
    global var_counter
    var_counter = 0

def new_var_name() -> str:
    global var_counter
    var_counter += 1
    return f'$@var{var_counter}'   # the `@` ensures that it is not a valid kurt variable

# rename all vars in `expr` with generated names to avoid clashes with other expressions
def rename_all_vars(expr: Expr, subst: Subst, kb: KnowledgeBase) -> tuple[Expr, Subst]:
    # `subst` contains the replacements so far, which are applied also down the AST
    match expr:

        # a token of an at least locally free variable will be replaced either by a known sub or with a new name
        case Token(label='SYMBOL', value=free_v) if isinstance(free_v, str) and kb.is_var(free_v):
            if free_v in subst:
                new_expr = subst[free_v]                 # replace with known substitution
            else:
                new_free_v = new_var_name()         # create new variable token
                new_expr = copy.deepcopy(expr)    # copy all meta infos, e.g. line, filename
                new_expr.value = new_free_v              # rename it
                subst[free_v] = new_expr                 # and store it in the `subst`
            return new_expr, subst

        # any other token is not modified
        case Token():
            return expr, subst

        # binding operators expression
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bound_v), *tail] if isinstance(op, str) and kb.is_bindop(op):
            new_bound_v = new_var_name()                 # in any case, `bound_v` gets a new name
            assert isinstance(expr[1], Token)
            new_bound_v_expr = copy.deepcopy(expr[1])
            new_bound_v_expr.value = new_bound_v
            local_subst = subst.copy()                   # we need a local `subst`, since the bound var is only changed locally
            assert isinstance(bound_v, str)
            local_subst[bound_v] = new_bound_v_expr           # store it for usage in this case, possibly overwrite a previous value
            new_expr, local_subst = rename_all_vars(expr[1:], local_subst, kb)   # includes the token of `bound_v`
            if bound_v in subst:
                local_subst[bound_v] = subst[bound_v]    # reset the value to the previous value, since `local_subst` will be returned
            else:
                del local_subst[bound_v]                 # else remove it, since it is elsewhere not used
            assert isinstance(new_expr, list)
            return [expr[0], *new_expr], local_subst

        # recursively replace the children
        case [*children] if len(children) > 0:
            new_expr = []
            for child in children:
                new_child, subst = rename_all_vars(child, subst, kb)
                new_expr.append(new_child)
            return new_expr, subst

    assert False, f'BUG: did not match expression `{expr}` in `rename_free_var`'

def generate_all_combinations(expr: Expr, token_x: Token, expr_a: Expr|None=None) -> Iterator[tuple[Expr|None, Expr]]:
    # generate all `($a, $A)` such that `expr = sub $x $a $A`
    if expr_a is None:
        # we still have full flexibility choosing `expr_a`
        yield None, expr            # $a=None, $A = expr
        yield expr, token_x         # $a=expr, $A = $x
    else:
        # `expr_a` has been chosen elsewhere, so we can not modify it
        yield expr_a, expr          # `expr` must not contain `token_x`
        if equal_expr(expr, expr_a):
            yield expr, token_x     # luckily, `expr` equals `expr_a`
    # if `expr` is a list, recursively build up the expression
    if isinstance(expr, list):
        if len(expr) > 0:
            for (cand_a, cand_A_0) in generate_all_combinations(expr[0], token_x, expr_a):
                for (cand_cand_a, cand_A_tail) in generate_all_combinations(expr[1:], token_x, cand_a):
                    assert isinstance(cand_A_tail, list)
                    yield cand_cand_a, [cand_A_0, *cand_A_tail]
        else:
            yield expr_a, []

def match_against_sub(expr: Expr, pattern: Expr, tail: list[tuple[Expr, Expr]], subst: Subst, kb: KnowledgeBase) -> Iterator[Subst]:
    match pattern:
        # `sub $x $a $A`
        case [Token(label='SYMBOL', value=sub_symbol), Token(label='SYMBOL', value=var_x), Token(label='SYMBOL', value=var_a), Token(label='SYMBOL', value=var_A)] \
            if isinstance(var_x, str) and isinstance(var_a, str) and isinstance(var_A, str) and kb.is_var(var_x) and kb.is_var(var_a) and kb.is_var(var_A):

            # find all combinations of `$a` and `$A` that match to `expr`
            token_x = pattern[1]
            assert isinstance(token_x, Token)
            for (expr_a, expr_A) in generate_all_combinations(expr, token_x):
                subst_local = subst.copy()
                if expr_a is not None:
                    subst_local[var_a] = expr_a                          # store the found substitutions for `$a`
                subst_local[var_A] = expr_A                          # store the found substitutions for `$A`
                yield subst_local

        # `sub $x expr_a $A`
        case [Token(label='SYMBOL', value=sub_symbol), Token(label='SYMBOL', value=var_x), expr_a, Token(label='SYMBOL', value=var_A)] \
            if isinstance(var_x, str) and isinstance(var_A, str) and kb.is_var(var_x) and kb.is_var(var_A):

            # find all variations of `$A` that match to `expr`
            token_x = pattern[1]
            assert isinstance(token_x, Token)
            for (expr_a, expr_A) in generate_all_combinations(expr, token_x, expr_a):
                subst_local = subst.copy()                               # shallow copy
                subst_local[var_A] = expr_A                              # store the constructed `$A`
                yield from match_exprs(tail, subst_local, kb)

        # `sub $x $a expr_A`
        case [Token(label='SYMBOL', value=sub_symbol), Token(label='SYMBOL', value=var_x), Token(label='SYMBOL', value=var_a), expr_A] \
            if isinstance(var_x, str) and isinstance(var_a, str) and kb.is_var(var_x) and kb.is_var(var_a):
            # match `expr` against `expr_A` and allow to replace `$x` in `expr_A` with anything
            subst_local = subst.copy()     # shallow copy
            if var_x in subst_local:
                del subst_local[var_x]                               # remove the current meaning of `$x`
            # we can freely choose what to put for `$x`, however, we can only choose once
            for subst_cand in match_exprs([(expr, expr_A)], subst_local, kb):
                if var_x in subst_local:                             # did we assign anything to `$x`?
                    assert var_a not in subst_local, f'BUG: is this a bug?  `$a` should not appear in `$A` after renaming'
                    subst_local[var_a] = subst_local[var_x]          # reassign the result to `$a`
                    del subst_local[var_x]                           # remove the assignment to the locally bound variable `$x`
                yield from match_exprs(tail, subst_cand, kb)

        # `sub $x expr_a expr_A`
        case [Token(label='SYMBOL', value=sub_symbol), Token(label='SYMBOL', value=var_x), expr_a, expr_A] if isinstance(var_x, str) and kb.is_var(var_x):
            subst_local = subst.copy()     # shallow copy
            subst_local[var_x] = expr_a
            yield from match_exprs([(expr, expr_A), *tail], subst_local, kb)

        # else case
        case _:
            # we didn't cover all cases!  bug!  either the outer `match` or the inner one failed
            assert False, f'BUG: `match_against_sub` did not cover all cases'

# each "case" with a recursive call has to loop over all generated local substitutions
# `exprs_patterns`:   [(e1, p1), (e2, p2), ...] = zip([e1, e2, ...], [p1, p2, ...])
# this list is necessary for the `[*_]` case, i.e., for matching two lists
def match_exprs(exprs_patterns: list[tuple[Expr, Expr]], subst: Subst, kb: KnowledgeBase) -> Iterator[Subst]:
    match exprs_patterns:

        case []:
            yield subst     # we found a substitution

        case [(expr, pattern), *tail]:
            # matches `expr` to `pattern` and extends `subst`
            match pattern:

                # variable matching
                case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
                    if v not in subst:
                        subst_local = subst.copy()     # shallow copy
                        subst_local[v] = expr          # extend the substitution
                        yield from match_exprs(tail, subst_local, kb)
                    elif equal_expr(subst[v], expr):
                        yield from match_exprs(tail, subst, kb)
                    else:
                        pass                           # no match possible, since `v` already assigned otherwise

                # symbol matching
                case Token(label=l, value=v):
                    if isinstance(expr, Token) and l==expr.label and v==expr.value:
                        yield from match_exprs(tail, subst, kb)

                # binding operator matching (rename bound variable)
                case [Token(label='SYMBOL', value=op_p), Token(label='SYMBOL', value=v_p), *args_p] if isinstance(op_p, str) and kb.is_bindop(op_p):
                    if op_p == sub_symbol:
                        # optionally: a pattern with a `sub` is special and possibly matches many expressions
                        yield from match_against_sub(expr, pattern, tail, subst, kb)
                    # in any case: additionally binding ops match against their matching binding ops
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), Token(label='SYMBOL', value=v_e), *args_e]:
                            if op_p==op_e and len(args_p)==len(args_e):
                                if v_p != v_e:
                                    # rename the bound variable
                                    args_p_local = copy.deepcopy(args_p)
                                    v_e_expr = expr[1]
                                    assert isinstance(v_p, str)
                                    args_p_local = [apply_subst(arg, {v_p:v_e_expr}, kb) for arg in args_p_local]
                                yield from match_exprs(list(zip(args_e, args_p_local)) + tail, subst, kb)
                                
                # list matching TODO when should subst be applied?
                case [*_] if isinstance(expr, list) and len(pattern)==len(expr):
                    pattern_tmp = copy.deepcopy(pattern)
                    pattern_tmp = [apply_subst(p, subst, kb) for p in pattern_tmp]
                    yield from match_exprs(list(zip(expr, pattern_tmp)) + tail, subst, kb)

        case _:
            # we didn't cover all cases!  bug!  either the outer `match` or the inner one failed
            assert False, f'BUG: `match_exprs` did not cover all cases for {exprs_patterns}'

# match a list of expressions against the theory and grow the substitution
def match_all_theory(exprs: list[Expr], subst: Subst, kb: KnowledgeBase) -> Subst | None:
    debug(exprs)
    match exprs:

        # we matched all `exprs`, done!
        case []:
            return subst
        
        # still at least one to go
        case [expr, *tail]:
            # deep copy of `expr` is necessary, since `match_all_theory` will be called several times with the same `exprs` in `impl_elim`
            # and we have to apply the "growing" set of substitutions to it
            expr_local: Expr = copy.deepcopy(expr)
            expr_local: Expr = apply_subst(expr_local, subst, kb)
            debug('expr_local', expr_local)
            # iterate over all formulas of the theory
            for candidate in kb.all_theory():
                # rename free and bound variables of `candidate` to avoid clashes with `expr_local`
                candidate_expr = rename_all_vars(copy.deepcopy(candidate.expr), {}, kb)[0]
                # iterate over all possible substitutions that create a match
                for subst_cand in match_exprs([(expr_local, candidate_expr)], subst, kb):
                    # try to match the rest of the expressions (the `tail`)
                    # (no deepcopy necessary, since in the next iteration `subst_cand` is overwritten)
                    subst_cand: Subst | None = match_all_theory(tail, subst_cand, kb)
                    if subst_cand is not None:
                        return subst_cand    # match was found!  BINGO!
            return None        # could not find a match among the candidate `patterns`

    # we calling `match_all_theory` wrongly, bug!
    assert False, f'BUG: `match_all_theory` did not cover all cases for {exprs}'

# what is happening:
# 0. deep copy `implication` and rename all its variables
# 1. split `implication` into `conclusion` and `premises`
# 2. match `expr` against `conclusion`
# 3. match `premises` against the theory (which needs to be renamed as well)
def impl_elim(expr: Expr, implication: Formula, kb: KnowledgeBase, filename: str, mainstream: bool) -> str | None:

    # to avoid overflow in the counter variable
    reset_var_name_counter()

    # deep copy and rename all variables
    # the renaming must happen before we cut the `implication` into pieces
    implication = copy.deepcopy(implication)
    implication_expr: Expr = rename_all_vars(implication.expr, {}, kb)[0]

    # assign `conclusion` and `premises`
    if is_implication(implication_expr):      # we have an implication with a premise
        assert isinstance(implication_expr, list)
        conclusion: Expr = implication_expr[2]
        match implication_expr[1]:

            # e.g., (A and B) implies C, then `premises = [A, B]`
            case [Token(label='SYMBOL', value=and_symbol), *premises]:
                pass                          # assigned already `premises` in the case matching

            # e.g., A implies C, then `premises = [A]`
            case premise:
                premises: list[Expr] = [premise]          # wrap a single premise in a list

    else:   # "implication" with an empty premise (think of `true implies $A`)
        conclusion = implication_expr
        premises   = []

    debug('con', conclusion)
    debug('pre', premises)

    # match `conclusion` and `premises`
    subst = None
    # iterate over all possible substitutions of the `conclusion`
    for subst in match_exprs([(expr, conclusion)], {}, kb):
        # no copy of `subst` necessary, since the next iteration will overwrite
        subst = match_all_theory(premises, subst, kb)
        if subst is not None:
            break           # bingo!  we found one
    if subst is None:
        return None         # no luck this time

    # create meaning full `reason`
    if kb.verbose:
        msg = 'BINGO!'
        msg += f'expression to prove: {expr_str(expr, kb)}'
        msg += f'implication used:    {expr_str(implication.expr, kb)}'
        msg += f'premises used:       {[expr_str(premise, kb) for premise in premises]}'
        msg += f'substitution used:   {subst}'
        print(msg, file=sys.stdout)
    restating = 'restating ' if len(premises) == 0 else ''
    if mainstream and implication.filename==filename:
        reason = f'by {restating}{implication.line}'
    else:
        reason = f'by {os.path.basename(implication.filename)}:{implication.line}'
    if implication.comment is not None:
        reason += f' {implication.comment}'
    return reason    # bingo!  found an implication

def derive_expr(e: Expr, kb: KnowledgeBase, filename: str, mainstream: bool) -> str:

    # first handle "top-intro"
    if isinstance(e, Token) and e.label=='SYMBOL' and e.value==true_symbol:
        return 'by top-intro'

    # iterate over the previously proven formulas that form the current theory
    for proven_formula in kb.all_theory():
        reason: str | None = impl_elim(e, proven_formula, kb, filename, mainstream)
        if reason is not None: 
            return reason

    # couldn't derive formula using any of the rules
    raise KurtException(f'ProofError: can not derive expression')

def scan_parse_check_eval(input_line: str, kb: KnowledgeBase, line: int, filename: str, mainstream:bool=False) -> KnowledgeBase:
    try:
        ts   = PeekableGenerator(scan_string(input_line))                                                   # lexer
        
        keyword_token, expr, comment = parse_tokenstream(ts, kb)       # parser
        kb   = eval_expression(keyword_token, expr, comment, kb, line, filename, mainstream) # evaluation
    except KurtException as e:
        e.filename = filename
        e.line     = line
        raise e
    return kb

def load_file(filename: str, kb: KnowledgeBase, markdown: bool=False, path: list[str]=theory_path, mainstream:bool=False) -> tuple[KnowledgeBase, bool]:
    # files are always loaded into level
    level = kb.level       # save current level
    if not filename.endswith('.kurt'):
        filename += '.kurt'
    try:
        fname = find_file(filename, path)    # search along the path
        if fname is None:
            raise OSError
        load_level = kb.get_load_level(fname)
        if load_level is not None:
            raise KurtException(f'EvalError: can not load library "{fname}" twice, it has already been loaded on level {load_level}')
        with open(fname) as f:
            kb, success = read_eval_loop(f, kb, markdown, mainstream=mainstream)
    except OSError as e:
        # we have to add `from None` to avoid exception chaining, since we only want to see the KurtException
        raise KurtException(f'EvalError: unable to open "{filename}" searching at {path}') from None
    
    if success:
        # checks after closing the file
        if kb.level != level:
            kb.level = level       # set levels back before raising the exception
            raise KurtException(f'\nEvalError: inside "{fname}" not all blocks closed, missing "end"?')
        if len(kb.show) != 0:
            s = '\nNot shown:\n'
            for f in kb.show:
                s += f'    {f.formula_str(kb):<{reason_indent-4}}; {os.path.basename(f.filename)}:{f.line}'
            raise KurtException(f'{s}\n\nEvalError: inside "{fname}" not all promised formulas were proved.')
        kb.libs.append(fname)
    else:
        raise KurtException(f'EvalError: inside "{fname}"', short=True)
    return kb, success

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

def read_eval_loop(input_stream: TextIO, kb: KnowledgeBase, markdown: bool=False, mainstream: bool=False):
    success   = True
    is_file   = (input_stream.name != '<stdin>')   # for non files we have a fancy prompt and we don't stop if an KurtException comes
    line       = 1
    continued  = False
    input_line = ''
    if not is_file:
        readline.parse_and_bind("tab: complete")    # Enable tab completion
    while True:
        try:
            if not is_file:
                prompt_text = prompt(kb.level, line, continued)
                new_line = input(prompt_text).rstrip()  # automatically uses readline
            else:
                new_line = input_stream.readline()
                if not new_line:
                    break
                new_line = new_line.rstrip()
            if markdown:
                if new_line.startswith(' ' * md_indent):
                    new_line = new_line[md_indent:]  # ignore the first `md_indent` spaces
                else:
                    continue
            input_line += new_line
            if input_line.endswith('\\'):    # line continuation possible with `\`
                input_line = input_line[:-1]
                continued = True
            else:
                try:
                    kb = scan_parse_check_eval(input_line, kb, line, input_stream.name, mainstream)
                except KurtException as e:
                    if e.short:
                        msg = e.msg
                    else:
                        if e.column is None: e.column = len(input_line)
                        if e.filename == '<stdin>':
                            msg = f'\n'
                        else:
                            msg = f'  File "{e.filename}", line {e.line}\n'
                        msg += f'    {input_line}\n'
                        msg += f'    {" " * e.column + "^"}\n'
                        msg += e.msg
                    print(msg, file=sys.stderr)
                    if is_file:
                        return kb, not success    # stop processing after the first error
                input_line = ''  # Reset input
                continued = False
                line += 1
        except EOFError:
            print("\nBye!", file=sys.stdout)      # this only happens when Ctrl-d is pressed in the interactive session
            break
    return kb, success

def find_file(fname: str, path: list[str]) -> str | None:
    for p in path:
        cand = os.path.join(p, fname)
        if os.path.isfile(cand):
            return cand
    return None

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=f'a simple proof assistant ({made_by})')
    parser.add_argument("filename", nargs='?',                       help=f'check the proof in the file, w/o filename start interactively')
    parser.add_argument('-i', '--interactive',  action='store_true', help=f'enter read-eval-print loop after loading `filename`')
    parser.add_argument('-m', '--markdown',     action='store_true', help=f'run on `.md` files instead of `.kurt`, will ignore everything that is not indented by {md_indent} spaces')
    parser.add_argument('-p', '--path',                              help=f'specify the path where `load` looks for theories after checking {theory_path}')
    parser.add_argument('-v', '--verbose',      action='store_true', help=f'show extra information during proof checking')
    parser.add_argument('-d', '--debug',        action='store_true', help=f'show debugging information')
    return parser.parse_args()

def main() -> None:
    args = parse_args()
    print(f'This is Kurt, Version {version} ({made_by})', file=sys.stdout)

    # debug flag?
    global debug_flag
    debug_flag = args.debug

    # readline history
    readline_history_file = os.path.expanduser("~/.kurt_history")         # should work on all platforms
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

    # by default load `default_theory` or nothing
    theory_filename = find_file(default_theory, theory_path)
    if theory_filename is not None:
        try:
            kb: KnowledgeBase = load_file(theory_filename, kb, mainstream=False)[0]
        except KurtException as e:
            print(e.msg, file=sys.stderr)

    # if there is a filename run the file
    if args.filename is not None:
        try:
            mainstream = not args.interactive
            kb, success = load_file(args.filename, kb, mainstream=mainstream)
            if success and mainstream:
                log('Proof checked.', None, kb)
        except KurtException as e:
            print(e.msg, file=sys.stderr)
    else:
        args.interactive = True

    # read-eval-print loop
    if args.interactive:
        kb : KnowledgeBase = read_eval_loop(sys.stdin, kb, mainstream=True)[0]
    exit(0)

if __name__ == "__main__":
    main()
