#!/usr/bin/env python3
from __future__ import annotations

## kurt.py
# kurt - a programming language for proof writing and checking
# (c) 2025 Stefan Harmeling
# licensed under the MIT License

## for profiling run:
# python -m cProfile -o kurt.prof kurt.py
# then analyze with:
# snakeviz kurt.prof
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
from ast import expr
import sys
if sys.version_info < (3, 10):
    print("Python 3.10 or newer is required, since we are using Python's `match`!  Sorry about that!", file=sys.stderr)
    exit(0)
import os           # os.path.[isfile, dirname, abspath, join, basename, split, expanduser, exists]
import io           # io.StringIO, for `EmbeddedTheories` (see `_EMBEDDED_THEORIES` below)
import argparse     # argparse.ArgumentParser
import re           # re.[compile, sub, VERBOSE, MULTILINE]
import atexit       # atexit.register
import inspect      # inspect.stack

import itertools    # itertools.[product, count, chain, permutations]
import json        # for `.kurtc` files, the certificates of a file
import copy        # copy.deepcopy, for the fresh context of a loaded file (`load_file`)
import contextlib  # contextlib.contextmanager, for `users_comment`
import time        # the dates of files, for `--deps`
from dataclasses import dataclass, field
from typing import TypeAlias, Literal, Callable, TypeVar, Generic, Iterator, TextIO, Optional, get_args
from pathlib import Path
from fractions import Fraction   # exact numbers for `calc`: `0.1` is 1/10
from importlib import resources

try:
    # should work under Linux and MacOS, but not under Windows
    import readline     # readline.[parse_and_bind, read_history_file, write_history_file]
except ImportError:
    # sorry, Windows users, no readline support
    # print("Warning: readline not available. Line editing features will be limited.")
    readline = None

try:
    import hashlib       # for `file_fingerprint()` below -- always in the stdlib, but some
except ImportError:      # exotic/stripped-down Python builds lack the C extension backing it
    hashlib = None

# config: general information
version        = 0.1
made_by        = 'made by Stefan Harmeling, 2025'

def file_fingerprint() -> str:
    # a short, self-verifying identifier for exactly which `kurt.py` is running. Unlike a
    # version number or a baked-in commit hash, this can never silently go stale: change one
    # byte of this file and the fingerprint changes right along with it -- so two people
    # comparing fingerprints can always tell whether they're really running the same code, no
    # matter which of the three ways they got this file (git checkout, the standalone bundle
    # from `scripts/build_standalone.py`, or a `pip install`). Best-effort by design: falls
    # back to 'unknown' rather than raising, since this is a diagnostic nicety, not something
    # any proof-checking logic depends on -- covers `__file__` being unavailable or unreadable
    # (some embedded/frozen environment) and `hashlib` being unavailable (some exotic build).
    if hashlib is None:
        return 'unknown'
    try:
        with open(__file__, 'rb') as f:
            content = f.read()
    except (NameError, OSError):
        return 'unknown'
    try:
        return hashlib.sha256(content).hexdigest()[:12]
    except Exception:
        return 'unknown'

# config: the indentation for the different blocks
proof_indent   =  4       # how much to indent for a `proof` block
comment_indent = 42       # how much the reason is indented
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
LOCAL_SYMBOL = 'local'       # marks a label (and its formula/def) as not exported by `load`

# not basic, but still necessary for our implementation of forall-intro and exists-intro
FORALL_SYMBOL = 'forall'     # universal quantification
EXISTS_SYMBOL = 'exists'     # existential quantification
EQUAL_SYMBOL  = '='          # equality
IFF_SYMBOL    = 'iff'        # equivalence

# symmetric operators whose arguments are never sorted, since `def` requires LHS and RHS to be in
# a certain order
SYM_KEEP_ORDER = [EQUAL_SYMBOL, IFF_SYMBOL]

# comparisons of two literal numbers that `calc on` evaluates to `true`/`false`
# the built-in calculator of `calc`: a theory binds its symbols to these, e.g. arith.kurt's
# `calc + add, * multiply, ...` -- only bound symbols are computed (see `calculate`)
# the largest numbers `calc` computes and the lexer reads (in digits): Python turns no bigger integer
# into a string, and powers of such numbers would take forever
MAX_NUMBER_DIGITS = 1000
MAX_NUMBER_BITS = int(MAX_NUMBER_DIGITS * 3.32)
CALCULATOR_OPERATIONS = ('add', 'subtract', 'negate', 'multiply', 'divide', 'power')
CALCULATOR_RELATIONS: dict[str, Callable[[Fraction, Fraction], bool]] = {
    'eq': lambda a, b: a == b,
    'ne': lambda a, b: a != b,
    'lt': lambda a, b: a < b,
    'le': lambda a, b: a <= b,
    'gt': lambda a, b: a > b,
    'ge': lambda a, b: a >= b,
}

# `_EMBEDDED_THEORIES` is populated (from `theories/*.kurt`) only in the generated single-file
# bundle produced by `scripts/build_standalone.py` -- empty here, in the real source file. It
# lets that bundle be a genuinely standalone `kurt.py`: download it alone and `load prop` (etc.)
# still works, no `theories/` directory required alongside it. See `EmbeddedTheories` below.
_EMBEDDED_THEORIES: dict[str, str] = {}

class _EmbeddedTheoryFile:
    def __init__(self, files: dict[str, str], name: str) -> None:
        self._files = files
        self._name = name
    def open(self, encoding: str = 'utf-8') -> io.StringIO:
        if self._name not in self._files:
            raise FileNotFoundError(self._name)
        f = io.StringIO(self._files[self._name])
        f.name = str(self)              # `read_eval_loop` needs `.name` (a real file always has one)
        return f
    def is_file(self) -> bool:
        return self._name in self._files
    def __str__(self) -> str:
        return f'<embedded>/{self._name}'

class EmbeddedTheories:
    # a minimal stand-in for a `Path`/`Traversable`, backed by an in-memory dict of theory
    # file contents -- supports exactly the operations `load_file` needs (`/`, `.open()`, `.is_file()`)
    def __init__(self, files: dict[str, str]) -> None:
        self._files = files
    def __truediv__(self, name: str) -> _EmbeddedTheoryFile:
        return _EmbeddedTheoryFile(self._files, name)
    def __str__(self) -> str:
        return '<embedded theories>'

# theory path
try:
    _packaged_theories = resources.files("kurt.theories")   # path of packaged theories, when installed
except (ModuleNotFoundError, ValueError):
    # `kurt.py` run standalone (`python3 kurt.py`, no install) -- `kurt` isn't an importable
    # package in that case, so fall back to a `theories/` directory next to this very file,
    # which is exactly what the README's "copy just kurt.py" classroom workflow expects. Also
    # catch `ValueError`: the kurt-web playground runs this exact file as a loose script inside
    # Pyodide's in-browser filesystem and independently needed to guard against a `ValueError`
    # from this same lookup there (reason unconfirmed -- likely a quirk of Pyodide's own
    # `importlib.resources` under WebAssembly -- but cheap to guard against regardless, since
    # this fallback already has a sensible default either way).
    _packaged_theories = Path(__file__).resolve().parent / "theories"
theory_path = [Path.cwd(),                             # current working directory
                          _packaged_theories]
packaged_theory_paths: list = [_packaged_theories]    # the theories that come with Kurt, see `packaged_theory_file`
if _EMBEDDED_THEORIES:
    theory_path.append(EmbeddedTheories(_EMBEDDED_THEORIES))   # last resort, only in the standalone bundle
    packaged_theory_paths.append(theory_path[-1])

def is_packaged_path(path) -> bool:
    return any(str(path) == str(p) for p in packaged_theory_paths)

# `--strict` (for grading): only trusted theory files may contain unproven statements
strict_mode: bool = False
trusted_paths: list = []       # the `-p`/`--path` directories, e.g. with a teacher's theories

def is_trusted_file(fname: str) -> bool:
    # a theory that comes with Kurt, or one from a `-p` directory -- the symbols they declare
    # are frozen (see `KnowledgeBase.frozen`), and under `--strict` only they may use `use`
    if fname.startswith('<embedded>/') or fname.startswith('<chain transitivity'):
        return True
    packaged = packaged_theory_file(os.path.basename(fname))
    if packaged is not None and str(packaged) == fname:
        return True
    try:
        parent = Path(fname).resolve().parent
    except (OSError, ValueError):
        return False
    return any(parent == Path(str(p)).resolve() for p in trusted_paths)

def check_not_frozen(ops: list[str], keyword: str, filename: str, kb: 'KnowledgeBase') -> None:
    # e.g. `sym -` or `chain ≠` would change what `-` or `≠` mean, which a trusted theory declared
    if is_trusted_file(filename):
        return
    for op in ops:
        if kb.is_frozen(op):
            raise KurtException(f'EvalError: `{keyword}` can not be declared for `{op}`, it would change the meaning of `{op}`, which comes with a theory of Kurt')

def check_chain_not_frozen(chain: list[str], filename: str, kb: 'KnowledgeBase') -> None:
    # a chain generates `$a op_i $b and $b op_j $c implies $a op_k $c`, with `op_k` the later
    # of the two -- an untrusted file may do that for its own operators, and combine them with
    # frozen ones (e.g. `chain = <` for its own `<`), but must not derive anything new about a
    # frozen operator (e.g. `chain ≠`, or `chain < =`)
    if is_trusted_file(filename):
        return
    frozen = [op for op in chain if kb.is_frozen(op)]
    if frozen != chain[:len(frozen)]:
        raise KurtException(f'EvalError: in `chain {" ".join(chain)}`, the operators that come with a theory of Kurt ({", ".join(frozen)}) must come first -- otherwise the chain would derive new facts about them')
    for i, a in enumerate(frozen):
        for b in frozen[i:]:
            if not any(a in c and b in c and c.index(a) <= c.index(b) for c in kb.all_chains()):
                if a == b:
                    raise KurtException(f'EvalError: `chain {" ".join(chain)}` would make `{a}` transitive, which comes with a theory of Kurt that doesn\'t declare it chainable')
                raise KurtException(f'EvalError: `chain {" ".join(chain)}` would change the meaning of `{a}` and `{b}`, which come with a theory of Kurt -- they aren\'t chained that way there')

def check_strict(keyword: str, filename: str) -> None:
    if strict_mode and not is_trusted_file(filename):
        raise KurtException(f'EvalError: `{keyword}` is not allowed with `--strict` -- everything must be proven from the theories that come with Kurt (or the ones given with `-p`)')

def packaged_theory_file(filename: str):
    # the packaged theory called `filename` (e.g. `prop.kurt`), if there is one -- those can't
    # be shadowed by a file of the same name elsewhere, since `def` and `--strict` rely on
    # their content (see `load_file`)
    if '/' in filename or '\\' in filename:
        return None
    for path in packaged_theory_paths:
        candidate = path / filename
        if candidate.is_file():
            return candidate
    return None

# debugging
debug_flag = False
debug_counter = 0
def debug(*s) -> None:
    if debug_flag:
        global debug_counter
        caller = inspect.stack()[1].function
        print(f'{debug_counter:03} DEBUG[{caller}]:', ' '.join(map(str, s)), file=sys.stdout)
        if debug_counter == 3630:
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
    '\\mapsto':   '↦',     # maps to
    '\\to':       '→',     # mapping arrow
    '\\times':    '×',     # Cartesian product
    '\\langle':   '⟨',     # angle brackets, e.g. for a scalar product `⟨a, b⟩`
    '\\rangle':   '⟩',

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

# match any known command inside the string (even if joined to other text, like `\cap\cup`) --
# but only a whole command: `\b` is `□`, but `\bot` is not `□ot`
COMMAND_RE = re.compile('(?:' + '|'.join(re.escape(k) for k in sorted(REPLACEMENTS, key=len, reverse=True)) + ')(?![A-Za-z])')

def replace_latex_syntax(line: str) -> str:
    def command_replacer(match: re.Match) -> str:
        command = match.group(0)
        return REPLACEMENTS.get(command) or command
    return COMMAND_RE.sub(command_replacer, line)

class KurtException(Exception):
    # every raise site still just writes its `kind` as a conventional string prefix
    # inside `msg` (e.g. `f'EvalError: ...'`), rather than passing `kind=` explicitly --
    # `.kind` is derived from that prefix here, once, so callers get a reliable
    # attribute to match on (see `expect`) without needing to touch the ~130
    # existing raise sites or parse `msg` themselves.
    KNOWN_KINDS = ('ProofError', 'ParseError', 'EvalError', 'SyntaxError', 'TypeError')

    def __init__(self, msg:str, column:Optional[int]=None, line:Optional[int]=None, filename:Optional[str]=None, kind:Optional[str]=None) -> None:
        self.msg:      str           = msg
        self.column:   Optional[int] = column
        self.line:     Optional[int] = line
        self.filename: Optional[str] = filename
        self.kind:     Optional[str] = kind if kind is not None else self._extract_kind(msg)
        self.kb_after: Optional['KnowledgeBase'] = None     # the level reached, if blocks were closed before the error

    @staticmethod
    def _extract_kind(msg: str) -> Optional[str]:
        stripped = msg.lstrip()
        for k in KurtException.KNOWN_KINDS:
            if stripped.startswith(k + ':'):
                return k
        return None    # message didn't start with (or wasn't prefixed by) a known kind

# types
Label:  TypeAlias = Literal['SYMBOL', 'INT', 'FLOAT', 'STRING', 'END', 'TODO']
Value:  TypeAlias = str | int | Fraction      # a number is an `int`, or an exact `Fraction` (a decimal like `0.1`)
Format: TypeAlias = Literal['sexpr', 'normal', 'original']
format_options: list[Format] = list(get_args(Format))  # sexpr: (+ 1 (* 3 4)), normal: (1 + (3 * 4))

## the syntax is stored in a hierarchical knowledge base called `KnowledgeBase`
keywords: dict[str, str] = {
    'help':        'print this help',
    'hint':        'print a hint for the next input',
    'verbose':     'toggle verbose mode, i.e., show extra information',
    'parse':       'parse a string and print its representation',
    'tokenize':    'tokenize a string and print its tokens',
    'format':      'choose print representation, i.e. one of "sexpr", "normal"',
    'level':       'print current level of the knowledge base',
    'mode':        'print current mode of the knowledge base, one of `root`, `sandbox`, `proof`, `assume`, `case`, `let`, `pick`, `expect`',
    'context':     'print the current context, i.e., all open blocks and their modes',
    'trail':       'print the current context without details in one line',
    'load':        'load file(s), e.g. load standards.kurt or load foo.kurt',
    'save':        'save the lines accepted so far (in the shell: without the ones that failed) as a `.kurt` file, e.g. save "session.kurt" (path is relative to the current working directory)',

    'syntax':      'print the current syntax',
    'prefix':      'add prefix operator with right binding power',
    'infix':       'add infix operator with left/right binding powers (lhb, rhb), note: lhb > rhb means right associative',
    'postfix':     'add postfix operator with left binding power',
    'brackets':    'declare brackets',
    'arity':       'set arity of a symbol (default is 0)',
    'bindop':      'declare a binding operator',
    'flat':        'declare infix operator to be flat',
    'sym':         'declare infix operator to be symmetric',
    'bool':        'declare symbols to have output type boolean',
    'calc':        'declare symbols to trigger calculations if applied to numbers',
    'chain':       'declare a chain of symbols, for automatic transitivity',
    'var':         'declare symbols as variable',
    'const':       'declare symbols as fresh constants, i.e., they have not been used or declared before',
    'alias':       'add some aliases for a symbol',
    'local':       'mark a label (on `use`/`show`/`def`) as local: the labelled formula/symbol is not exported when this file is `load`ed elsewhere, e.g. `use %A implies %A local "restatement"`',

    'theory':      'print all formulas, or print formulas that have a certain top level symbol',
    'cert':        'show the certificates of a line in long form, as checked by the kernel, e.g. `cert 17`; without a number, of the last line with a step',

    # formulas
    'use':         'use a formula without proof as a axiom',
    'def':         'define new constant symbol using an equation or equivalence',

    'show':        'plan to prove a formula',
    'proof':       'start a proof block to prove the last planned formula',
    'qed':         'end a proof block, to finish the proof of the last planned formula (optional -- dedenting alone already does this; `qed` documents it and double-checks you meant to close a `proof`, not some other kind of block)',

    'todo':        'without a formula it is a joker for the next one, with a formula it is a joker for that one',

    # opening blocks (besides `proof`)
    'assume':      'open a block and assume a formula (made for "impl-intro" and "not-intro"), block must be indented',
    'case':        'open a case analysis block for disjunctions (made for "or-elim"), block must be indented',
    'let':         'fix a new constant, possibly with an assumption (made for "forall-intro"), block must be indented',
    'pick':        'pick a new constant "with" assumption (made for "exists-elim"), block must be indented',
    'sandbox':     'open a temporary block, useful for trying out things; discarded when closed, whether by dedenting or by `break`',
    'expect':      'open a block whose content must raise the named kind of error (one of ProofError, ParseError, EvalError, SyntaxError, TypeError) to succeed -- anywhere inside, including in nested blocks and while they close; the block is discarded either way',

    # closing a block explicitly (besides just dedenting, which works everywhere and is enough on its own)
    'break':       'discard the current block immediately (no proof step, no dedent needed)',

    # inspection for files
    'inspect':     'stop executing a file and start the shell',
    }
helper_keywords = ['with']     # for keyword `pick`, e.g., `pick y with F(y)`

keywords_with_parsing = ['use', 'show', 'def', 'assume', 'case', 'let', 'todo', 'parse']
keywords_opening_blocks = ['proof', 'assume', 'case', 'let', 'pick', 'sandbox', 'expect']
keywords_closing_blocks = ['qed', 'break']

@dataclass
class Token:
    label: Label
    value: Value
    column: Optional[int] = None
    origin: Optional[Value] = None
    chained: bool = False    # an `and` created by `chain_relations`, only needed while parsing

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

def clean_up(line: str) -> str:
    if line == '':
        return line
    line = line.strip()
    line = line.split(';')[0]   # remove comments
    pieces = line.split(' ')
    pieces = [p for p in pieces if p != '']   # remove empty pieces
    if pieces[0] in keywords:
        line = ' '.join(pieces[1:])  # remove the keyword
    return line

class Formula:
    next_id: int = 0
    def __init__(self, kb: KnowledgeBase, expr:Expr, input_line:str, line:str, filename:str, label:str, reason:str, keyword:str, local:bool = False):
        self.expr: Expr            = expr               # expression of the formula
        self.simplified_expr       = expr               # will be simplified later when adding to the knowledge base
        self.input_line: str       = clean_up(input_line) # original input line of this formula, before any simplification
        self.line: str             = line               # line number of this formula, type string since we also want '16a', etc
        self.filename: str         = filename           # file of this formula
        self.label: str            = label              # basically, a name of the formula, e.g., "impl-intro"
        self.reason: str           = reason             # the reason for this formula, e.g., "axiom", "assumption", "def", "by"
        self.keyword: str          = keyword            # one of `use`, `assume`, `show`, `todo`
        self.local: bool           = local              # `label local "..."`: not exported when this file is `load`ed elsewhere
        self.def_symbol: Optional[str] = None           # for `def`-created formulas: the symbol it defines (see `eval_def`)
        self.direction_of: Optional[Expr] = None        # for `L ⇒ R` made from an `iff`: that `iff` (see `impl_elim`)
        self.id: int               = Formula.next_id    # a unique id for every formula
        Formula.next_id += 1

    def is_proven(self) -> bool:
        # proven if `self.keyword in ['', 'todo']`
        # not proven is `self.keyword in ['use', 'show']`
        return self.keyword in ['', 'todo']

    def is_exported(self) -> bool:
        # see doc/kurt-doc.md's `load` section: a labelled, non-`local` fact is exported
        # when this file is `load`ed elsewhere; an unlabelled or `local`-labelled one isn't
        return len(self.label) > 0 and not self.local

    def clone(self, new_expr: Expr, kb: KnowledgeBase) -> Formula:
        cloned_f = Formula(
            kb,
            expr       = new_expr,
            input_line = self.input_line,
            line       = self.line,
            filename   = self.filename,
            label      = self.label,
            reason     = self.reason,
            keyword    = self.keyword,
            local      = self.local
        )
        cloned_f.id = self.id
        cloned_f.def_symbol = self.def_symbol
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
        if kb.format == 'original':
            s = self.input_line
        else:
            s = expr_str(self.expr, kb)
        return f'{self.prefix_str()}{s}'

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
    # the fresh variables standing for the bound variable of a `forall` premise: no variable of
    # the rule (the pattern side) may take a value containing one -- except a boolean `%A`,
    # which may depend on it by definition -- see `block_eigen`
    eigen: frozenset[str] = frozenset()

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
        new_subst = dict(self.subst)   # shallow copy -- `subst` only ever grows one key at a
        # time, and stays small in practice (schema variables per match), so a plain dict copy
        # here is both simpler and, measured directly, at least as fast as a persistent/chained
        # alternative would be for kurt's actual proof files -- see doc/kurt-soundness.md #6 for
        # why a linked-frame version was tried and reverted (it trades this O(n) copy for O(depth)
        # lookups, which loses badly once a derivation accumulates more than a handful of bindings)
        assert not self.occurs(v, e), f'occurs check failed: cannot bind {v} to {e}'
        new_subst[v] = deepcopy_expr(e)
        return State(new_subst, self.blocked_as_domain, self.blocked_as_range, self.eigen)

    def block_as_domain(self, v: str) -> State:
        # this is for free variables of the goal, e.g.,
        #   use A, B ⇒ C
        #   D
        # to prove D we first unify D with C, but must block the free variables of D as domain
        # (`subst` itself is untouched by this, and immutable, so it's shared as-is, not copied)
        return State(self.subst, self.blocked_as_domain | {v}, self.blocked_as_range, self.eigen)

    def block_always(self, v: str) -> State:
        # this is for blocking bound variables
        return State(self.subst, self.blocked_as_domain | {v}, self.blocked_as_range | {v}, self.eigen)

    def unblock(self, v: str) -> State:
        return State(self.subst, self.blocked_as_domain - {v}, self.blocked_as_range - {v}, self.eigen)

    def block_eigen(self, v: str) -> State:
        # a fresh variable for the bound variable of a premise `forall $x ...`: it stands for an
        # arbitrary object, so it must not be assigned (blocked as domain), and no other variable
        # of the rule may take a value containing it -- e.g. `$T` in `(forall $x ($x = $T))
        # implies Q` is one fixed term, `$T := v ^ 1` would make it depend on `$x`
        return State(self.subst, self.blocked_as_domain | {v}, self.blocked_as_range, self.eigen | {v})

    def contains_eigen(self, e: Expr) -> bool:
        e = self.walk(e)
        if isinstance(e, Token):
            return isinstance(e.value, str) and e.value in self.eigen
        return any(self.contains_eigen(c) for c in e)

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

def is_numeric(e: Expr) -> bool:
    match e:
        case Token(label='INT', value=_):
            return True
        case Token(label='FLOAT', value=_):
            return True
        case _:
            return False

def number_str(v: Value) -> str:
    # an exact decimal, e.g. `0.25` for 1/4 (the numbers kept as a `Fraction` token are decimals)
    if not isinstance(v, Fraction):
        return str(v)
    if v.denominator == 1:
        return str(v.numerator)
    digits = 0
    while (v * 10 ** digits).denominator != 1:
        digits += 1
    scaled = abs(v.numerator * 10 ** digits // v.denominator)
    text = str(scaled).rjust(digits + 1, '0')
    return ('-' if v < 0 else '') + text[:-digits] + '.' + text[-digits:]

def is_decimal(v: Fraction) -> bool:
    # whether `v` has a finite decimal expansion (its denominator has only the factors 2 and 5)
    d = v.denominator
    for p in (2, 5):
        while d % p == 0:
            d //= p
    return d == 1

def number_expr(v: int | Fraction, kb: 'KnowledgeBase') -> Optional[Expr]:
    # a number as an expression: an integer, a decimal, or a fraction `1 / 3` with the symbol
    # bound to `divide` (`None` if there is none, or if the number is too big, see `MAX_NUMBER_BITS`)
    v = Fraction(v)
    if v.numerator.bit_length() > MAX_NUMBER_BITS or v.denominator.bit_length() > MAX_NUMBER_BITS:
        return None
    if isinstance(v, int) or v.denominator == 1:
        return Token(label='INT', value=int(v))
    if is_decimal(v):
        return Token(label='FLOAT', value=v)
    div = kb.calc_symbol('divide')
    if div is None:
        return None
    return [Token(label='SYMBOL', value=div), Token(label='INT', value=v.numerator), Token(label='INT', value=v.denominator)]

def number_value(e: Expr, kb: 'KnowledgeBase') -> Optional[int | Fraction]:
    # the value of a number: an integer, a decimal, or a fraction `1 / 3` (see `number_expr`)
    if is_numeric(e):
        assert isinstance(e, Token) and not isinstance(e.value, str)
        return e.value
    match e:
        case [Token(label='SYMBOL', value=op), Token(label='INT', value=a), Token(label='INT', value=b)] \
                if isinstance(op, str) and 'divide' in kb.get_calc_ops(op) and isinstance(a, int) and isinstance(b, int) and b != 0:
            return Fraction(a, b)
    return None

def calculate(e: Expr, kb: 'KnowledgeBase') -> Expr:
    # compute the operations on numbers whose symbols are bound to the calculator (`calc`), exactly
    if isinstance(e, Token):
        return e
    assert isinstance(e, list) and len(e) > 0, f'BUG: unexpected expression `{e}`'
    e = [calculate(sub_e, kb) for sub_e in e]         # the parts first
    match e:
        case [Token(label='SYMBOL', value=op), *args] if isinstance(op, str) and args:
            ops = kb.get_calc_ops(op)
            if not ops:
                return e
            values = [number_value(a, kb) for a in args]
            numbers = [v for v in values if v is not None]
            others = [a for a, v in zip(args, values) if v is None]
            if ('add' in ops or 'multiply' in ops) and len(args) >= 2 or (len(args) >= 1 and kb.is_flat(op) and ('add' in ops or 'multiply' in ops)):
                if not numbers:
                    return e
                if 'add' in ops:
                    total: Fraction = sum((Fraction(n) for n in numbers), Fraction(0))
                    if total == 0 and others:           # `0 + x` is `x`
                        return others[0] if len(others) == 1 else [e[0], *others]
                else:
                    total = Fraction(1)
                    for n in numbers:
                        total *= n
                    if total == 0:                      # `0 * x` is `0` ("mul-zero")
                        return Token(label='INT', value=0)
                    if total == 1 and others:           # `1 * x` is `x`
                        return others[0] if len(others) == 1 else [e[0], *others]
                if len(numbers) == 1 and others:
                    return e                            # nothing to compute
                number = number_expr(total, kb)
                if number is None:
                    return e
                return number if not others else [e[0], number, *others]
            if len(args) == 1 and 'negate' in ops and numbers:
                return number_expr(-Fraction(numbers[0]), kb) or e
            if len(args) == 2 and len(numbers) == 2:
                a, b = Fraction(numbers[0]), Fraction(numbers[1])
                if 'subtract' in ops:
                    return number_expr(a - b, kb) or e
                if 'divide' in ops:
                    if b == 0:
                        return e                        # `1 / 0` is not computed
                    return number_expr(a / b, kb) or e
                if 'power' in ops:
                    # only integer exponents, not too big: `2 ^ 0.5` has no exact value, and
                    # `0 ^ -1` and `0 ^ 0` none at all (arith.kurt leaves `0 ^ 0` open)
                    if b.denominator != 1 or (a == 0 and b <= 0):
                        return e
                    size = max(a.numerator.bit_length(), a.denominator.bit_length())
                    if size > 1 and (size - 1) * abs(b) > MAX_NUMBER_BITS:
                        return e                        # the result would be too big
                    return number_expr(a ** int(b), kb) or e
    return e

# what a loaded file passes on to the file that loads it (see `KnowledgeBase.merge_and_pop`):
# exactly the fields below -- a field of `KnowledgeBase` that isn't here stays in the file, so a
# new one is local unless it is added here (codex-suggestions.md, 2026-09-29)
#
# SELECTIVE EXPORT: only labelled, non-`local` facts -- and whatever symbol declarations they
# actually need -- travel to the parent (see doc/kurt-doc.md's `load` section,
# doc/kurt-soundness.md #7). An unlabelled or `local`-labelled fact stays entirely inside the
# file; a symbol only ever mentioned by such facts is invisible from outside too.
@dataclass
class ExportBundle:
    theory: list['Formula']                  # the exported facts, in their order
    symbols: set[str]                        # the symbols they need (and their aliases, brackets)
    infix: dict[str, tuple[int, int]]
    postfix: dict[str, int]
    prefix: dict[str, int]
    brackets: dict[str, str]
    arity: dict[str, int]
    bindop: set[str]
    flat: set[str]
    sym: set[str]
    alias: dict[str, str]
    used: set[str]
    lbp: dict[str, int]
    rbp: dict[str, int]
    nud: dict[str, 'Nud']
    led: dict[str, 'Led']
    const: set[str]
    bool: dict[str, list[int]]
    calc_ops: dict[str, list[str]]
    chain: list[list[str]]
    frozen: set[str]                         # the symbols a trusted theory declared (`is_trusted_file`)
    libs: list[str]                          # the files it loaded
    todos: list[str] = field(default_factory=list)   # its open `todo`s

# the fields of `ExportBundle` that are symbol-keyed attributes of `KnowledgeBase`, of this level only
EXPORTED_SYMBOL_ATTRS = ('infix', 'postfix', 'prefix', 'brackets', 'arity', 'bindop', 'flat', 'sym', 'alias',
                         'used', 'lbp', 'rbp', 'nud', 'led', 'const', 'bool', 'calc_ops', 'frozen')

def exported_formulas_and_symbols(child: 'KnowledgeBase') -> tuple[list['Formula'], set[str]]:
    exported = [f for f in child.theory if f.is_exported()]
    symbols: set[str] = set()
    for f in exported:
        symbols |= free_symbols(f.expr, child)
    # custom brackets are special: what actually shows up in a parsed expression is the synthetic
    # combined token (`{lbracket}$$${rbracket}`), but the pair's own const/nud/lbp entries are
    # keyed by the raw bracket characters -- pull those in too once the pair is needed
    for rbracket, lbracket in child.brackets.items():
        if f'{lbracket}$$${rbracket}' in symbols:
            symbols |= {lbracket, rbracket}
    # aliases are pure syntax sugar for an existing symbol -- axioms are written with the
    # canonical name (e.g. `not`), so an alias (`¬`) never itself "occurs" in a formula: pull in
    # any alias whose target is exported, to a fixed point in case aliases chain
    changed = True
    while changed:
        changed = False
        for alias_name, target in child.alias.items():
            if target in symbols and alias_name not in symbols:
                symbols.add(alias_name)
                changed = True
    return exported, symbols

def compute_exports(child: 'KnowledgeBase') -> ExportBundle:
    # what `child` (the level of a loaded file) exports -- copies, nothing shared with `child`
    exported, symbols = exported_formulas_and_symbols(child)
    def select(attr: str):
        value = getattr(child, attr)
        if isinstance(value, dict):
            return {k: (list(v) if isinstance(v, list) else v) for k, v in value.items() if k in symbols}
        assert isinstance(value, set), f'BUG: unexpected type for {attr}: {type(value)}'
        return {s for s in value if s in symbols}
    return ExportBundle(theory=list(exported), symbols=set(symbols),
                        **{attr: select(attr) for attr in EXPORTED_SYMBOL_ATTRS},
                        chain=[list(c) for c in child.chain if all(op in symbols for op in c)],
                        libs=list(child.libs))

def validate_exports(bundle: ExportBundle, child: 'KnowledgeBase', parent: 'KnowledgeBase', own_file: Optional[str]) -> None:
    # an exported fact of the file itself must not need a `local` definition -- exporting a fact
    # without what its symbol means would smuggle out what the author marked private
    local_def_symbols = {f.def_symbol for f in child.theory if f.def_symbol is not None and not f.is_exported()}
    own_symbols: set[str] = set()
    for f in bundle.theory:
        if own_file is None or f.filename == own_file:
            own_symbols |= free_symbols(f.expr, child)
    leaked = local_def_symbols & own_symbols
    if leaked:
        raise KurtException(f'EvalError: symbol(s) {sorted(leaked)} are defined `local` but required by an exported fact -- export their `def` too, or keep them out of exported facts')
    # a loaded constant can't be a variable of the loading file (`var y`, then `load` a file with `const y`)
    clash = sorted(sym for sym in bundle.symbols if sym in bundle.const and parent.is_var(sym) and sym[0] not in '$%')
    if clash:
        raise KurtException(f'EvalError: {", ".join(f"`{c}`" for c in clash)} is a constant of the loaded file, but a variable here -- load the file before `var`, or rename the variable')

def apply_exports(parent: 'KnowledgeBase', bundle: ExportBundle) -> None:
    # add the exports to `parent`, the level that loaded the file -- what `parent` has already
    # (from a file that both loaded) only once
    known = {(f.filename, f.line, f.label) for node in parent.levels() for f in node.theory}
    parent.theory.extend(f for f in bundle.theory if (f.filename, f.line, f.label) not in known)
    for attr in EXPORTED_SYMBOL_ATTRS:
        getattr(parent, attr).update(getattr(bundle, attr))
    parent.chain.extend(c for c in bundle.chain if c not in parent.all_chains())
    parent.libs.extend(lib for lib in bundle.libs if parent.get_load_level(lib) is None)
    if bundle.calc_ops:
        parent.all_calc_ops = {**parent.all_calc_ops, **{sym: list(ops) for sym, ops in bundle.calc_ops.items()}}

# hierarchical knowledge base
# the level is increased inside blocks and files
# dropping a level drops also all local definitions
Nud: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Token], Expr]
Led: TypeAlias = Callable[[PeekableGenerator, "KnowledgeBase", Expr, Token], Expr]
Mode: TypeAlias = tuple[str, list[Expr]]  # where the str is one of ['root', 'sandbox', 'proof', 'assume', 'case', 'let', 'pick', 'expect']

class KnowledgeBase:
    def __init__(self, parent:Optional[KnowledgeBase], mode: Mode, tmp: bool = False) -> None:
        # general
        self.parent: Optional[KnowledgeBase] = parent
        self._todos: list[str]      = []         # list of todos (only relevant on level 0, all todos are collected there)
        self.level: int             = 0 if parent is None else parent.level + 1
        self.mode_str: str          = mode[0]    # one of ['root', 'sandbox', 'proof', 'assume', 'case', 'let', 'pick', 'expect']
        self.mode_args: list[Expr]  = mode[1]    # expression that opened the current block (just [] for 'root', 'sandbox', 'proof')
        self.pick_source: Optional[Formula] = None   # for a `pick` block: the existential fact it picks from
        self.fixed_vars: set[str] = set()            # for an `assume`/`case` block: the free variables of the assumption (see `is_var`)
        self.let_names: list[str] = []               # for a `let` block: its new constants, in order
        self.all_fixed_vars: frozenset[str] = frozenset() if parent is None else parent.all_fixed_vars   # ... of this and the enclosing blocks
        self.pick_fact: Optional[Formula]   = None   # ... and the fact about the witness (for the kernel)
        self.libs: list[str]        = []         # the filenames of loaded libraries
        self.tmp: bool              = tmp        # whether this is a temporary knowledge base (e.g., for loading files this enable correct indenting)
        self.is_load_boundary: bool = False      # set only on the implicit `sandbox` level `load_file` itself
                                                  # pushes for the file being loaded -- `break` must
                                                  # refuse to close this one (there's no real, user-written
                                                  # block here to close), or `load_file`'s own bookkeeping
                                                  # (it expects to be the only one popping this exact level)
                                                  # breaks with an internal `assert False`, not a clean error

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
        self.frozen:   set[str]                  = set()  # symbols declared by a trusted theory, see `is_trusted_file`
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
                                                          #                   assumptions added by 'assume' or 'case',
                                                          #                   and derived formulas)
        self.show:   list[Formula] = []                   # lists of promised formulas to show

        # global options stored in the `root` with their defaults
        self.format:  Format = format_options[1] if parent is None else parent.format  # how formulas look in the shell
        self.verbose: bool   = False if parent is None else parent.verbose             # show extra information or not
        self.calc:    bool   = False if parent is None else parent.calc                # whether to perform calculations inside expressions
        self.calc_ops: dict[str, list[str]] = {}                                      # symbol -> the calculator's operations it is bound to (`calc + add`)
        self.all_calc_ops: dict[str, list[str]] = {} if parent is None else parent.all_calc_ops   # ... of this and the levels above (never changed in place)
        self.hint:    bool   = False if parent is None else parent.hint                # whether to show hints for next input

    def check_all_shown_proved(self):
        if len(self.show) > 0:                  # any planned formulas inside the current proof?
            s = '\nNot shown:\n'
            for f in self.show:
                s += f'    {f.formula_str(self):<{comment_indent-4}}; {os.path.basename(f.filename)}:{f.line}'
            raise KurtException(f'{s}\n\nEvalError: not all promised formulas were proven.')

    def get_calc_ops(self, symbol: str) -> list[str]:
        # the calculator's operations `symbol` is bound to (`calc`), in this level or above
        return self.all_calc_ops.get(symbol, [])

    def calc_symbol(self, operation: str) -> Optional[str]:
        # the symbol bound to `operation`, e.g. `/` for `divide`
        for symbol, ops in self.all_calc_ops.items():
            if operation in ops:
                return symbol
        return None

    def bind_calc(self, symbol: str, operation: str) -> None:
        # one operation per symbol -- and a unary one, `negate`, besides (like `-`); `calc q power,
        # q add` silently computed `add` (found in the soundness review of 2026-09-29)
        others = [op for op in self.get_calc_ops(symbol) if op != operation and (op == 'negate') == (operation == 'negate')]
        if others:
            raise KurtException(f'EvalError: `{symbol}` is bound to `{others[0]}` already, it can not also mean `{operation}`')
        ops = self.calc_ops.setdefault(symbol, [])
        if operation not in ops:
            ops.append(operation)
        self.all_calc_ops = {**self.all_calc_ops, symbol: list(ops)}

    def calculate(self, e: Expr) -> Expr:
        """If e is a calculation expression, perform the calculation and return the simplified expression."""
        return calculate(e, self)

    def push_level(self, mode_str: str, mode_expr_list: list[Expr]) -> KnowledgeBase:
        return KnowledgeBase(parent=self, mode=(mode_str, mode_expr_list), tmp=self.tmp)

    def pop_level(self) -> KnowledgeBase:
        if self.level == 0:
            raise KurtException(f'EvalError: no block to close')
        self.check_all_shown_proved()  # check that all `show` formulas have been proved
        assert self.parent is not None, f'BUG: we should be one level up'
        parent = self.parent
        self.parent = None        # detaching it might help the garbage collector
        return parent

    def merge_and_pop(self, own_file: Optional[str] = None) -> KnowledgeBase:
        # the end of a loaded file: pass on its exports (only those, see `ExportBundle`) to the
        # level that loaded it (`own_file`: the file whose level this is -- a fact it only passes
        # on from a file it loaded can't depend on its `local` definitions)
        assert self.parent is not None, f'BUG: cannot merge and pop a level without a parent'
        if len(self.show) > 0:
            raise KurtException(f'EvalError: cannot merge and pop a level with promised formulas, got {len(self.show)} formulas.')
        bundle = compute_exports(self)
        validate_exports(bundle, self, self.parent, own_file)
        apply_exports(self.parent, bundle)
        return self.pop_level()

    def nice_mode_str(self) -> str:
        args_str = ", ".join([f'{expr_str(v, self)}' for v in self.mode_args]) if len(self.mode_args) > 0 else ''
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
            return self.parent.todos()

    def loaded_files_str(self) -> str:
        lines = self._loaded_files_lines()
        return '\n'.join(lines) if len(lines) > 0 else '; no files loaded'

    def _loaded_files_lines(self) -> list[str]:
        lines = self.parent._loaded_files_lines() if self.parent is not None else []
        return lines + [f'load {lib:<{comment_indent}}; level {self.level}' for lib in self.libs]

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

        # put the level at the `comment_indent` column
        lines = [f'{line:<{comment_indent}}; level {self.level}' for line in lines]
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
            return f'; `{number_str(value)}` is a decimal number'
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


    def is_fixed_var(self, s: str) -> bool:
        return s in self.all_fixed_vars

    def is_var(self, s: str) -> bool:
        # is_var checks whether a symbol is a variable (could be non-boolean or boolean) --
        # except the free variables of an assumption in its block, which are fixed there: in
        # `assume P $x`, `$x` is one (arbitrary) object, until the block closes (`P $x ⇒ ...`)
        if self.is_fixed_var(s):
            return False
        if s in self.const:
            assert s not in self.var
            return False
        elif s[0] in ['$', '%']:
            return True
        elif s in self.var:
            return True
        else:
            return self.parent is not None and self.parent.is_var(s)

    def is_local_var(self, s: str) -> bool:                # check only in the current level, used for `add_const`
        return s in self.var

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

    def get_chain_op(self, chain_so_far: list[Token]) -> Optional[Token]:
        # find the chain that matches `chain_so_far` and return the operator that is at the largest index matched so far
        for c in self.all_chains():
            max_index: int = -1
            max_op: Optional[Token] = None
            for op in chain_so_far:
                assert isinstance(op.value, str)
                if op.value in c:
                    if c.index(op.value) >= max_index:     # e.g. `a = b < c = d` gives `a < d`
                        max_index = c.index(op.value)
                        max_op = op
                else:
                    max_index = -1
                    max_op = None
                    break
            if max_op is not None:   # all ops were found, return the one with the largest index
                return max_op
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

    def is_frozen(self, s: str) -> bool:
        return s in self.frozen  or (self.parent is not None and self.parent.is_frozen(s))

    def declared_symbols(self) -> set[str]:
        # every symbol declared on this level (not the parents)
        symbols = set(self.infix) | set(self.prefix) | set(self.postfix) | set(self.bindop) | set(self.const)
        symbols |= set(self.bool) | set(self.arity) | self.flat | self.sym | set(self.alias)
        return symbols

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
        return 0 in self.bool_sig(s)  or  s[0] == '%'

    def is_lbracket(self, s: str) -> bool:
        return s in self.brackets.values() or (self.parent is not None and self.parent.is_lbracket(s))

    def is_rbracket(self, s: str) -> bool:
        return s in self.brackets.keys() or (self.parent is not None and self.parent.is_rbracket(s))

    def is_bracket(self, s: str) -> bool:
        return self.is_lbracket(s) or self.is_rbracket(s)

    def is_bracket_placeholder(self, s: str) -> bool:
        # split `s` into `left` + `$$$` + `right`
        parts = s.split('$$$')
        if len(parts) != 2:
            return False
        left, right = parts
        return self.is_lbracket(left) and self.is_rbracket(right)

    def is_declared(self, s: str) -> bool:
        # declared in some way before its first use, e.g. by `bool A`, `arity f 1`, `infix + 60 60`
        return (self.is_var(s) or self.is_const(s) or len(self.bool_sig(s)) > 0 or self.is_arity_set(s)
                or self.is_operator(s) or self.is_bindop(s) or self.is_alias(s))

    def is_operator(self, s: str) -> bool:
        return self.is_prefix(s) or self.is_infix(s) or self.is_postfix(s) or self.is_bracket(s)

    def is_vocabulary_symbol(self, s: str) -> bool:
        # true for a symbol that names something globally meaningful (a function, a
        # predicate, an operator, or a boolean proposition) rather than a fresh
        # individual object -- used by `assume`/`let`/`pick`'s "did a fresh constant
        # from this block escape into the conclusion?" check (see `eval_done` in
        # `eval_done`/`eval_pick`) to tell apart, e.g., a predicate symbol `P` that
        # happens to be *first used* inside the block (fine, it's not scoped to it)
        # from a genuinely fresh individual like a `let`/`pick`/`const`-introduced
        # constant (not fine, it must not survive past the block it came from)
        return self.get_arity(s) > 0 or self.is_operator(s) or self.is_bindop(s) or self.is_bool(s)

    def levels(self) -> Iterator['KnowledgeBase']:
        # this level and the ones above it
        node: Optional[KnowledgeBase] = self
        while node is not None:
            yield node
            node = node.parent

    def lookup(self, attr: str, s: str):
        # the entry for `s` in the dict `attr` of the innermost level that has one
        for node in self.levels():
            table = getattr(node, attr)
            if s in table:
                return table[s]
        return None

    def get_infix(self, s: str) -> Optional[tuple[int, int]]:   return self.lookup('infix', s)
    def get_prefix(self, s: str) -> Optional[int]:              return self.lookup('prefix', s)
    def get_postfix(self, s: str) -> Optional[int]:             return self.lookup('postfix', s)
    def get_lbracket(self, s: str) -> Optional[str]:            return self.lookup('brackets', s)

    def is_known(self, s: str) -> bool:
        # whether `s` is declared or used somewhere on this level or above
        return any(s in node.declared_symbols() or s in node.used or s in node.brackets.values() for node in self.levels())

    def get_arity(self, fun: str) -> int:
        if fun in self.arity:
            return self.arity[fun]
        elif self.parent is not None:
            return self.parent.get_arity(fun)
        else:
            return 0

    def is_arity_set(self, fun: str) -> bool:
        # unlike `get_arity(fun) > 0`, this also correctly reports symbols explicitly
        # declared with arity 0, and is what "already declared" guards must use --
        # `fun in self.arity` alone only checks the *current* level, not ancestors
        return fun in self.arity or (self.parent is not None and self.parent.is_arity_set(fun))

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
        if self.is_used(fun):
            raise KurtException(f'EvalError: symbol `{fun}` has been already used in a formula, declaring it now would change what that formula means')
        if self.is_prefix(fun):
            raise KurtException(f'EvalError: arity of prefix operators is one and can not be set')
        if self.is_postfix(fun):
            raise KurtException(f'EvalError: arity of postfix operators is one and can not be set')
        if self.is_infix(fun):
            raise KurtException(f'EvalError: arity of infix operators is two and can not be set')
        if self.is_bracket(fun):
            raise KurtException(f'EvalError: arity of brackets can not be set')
        if self.is_arity_set(fun):
            raise KurtException(f'EvalError: arity of symbol `{fun}` has been already set to {self.get_arity(fun)}')
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
        if self.is_used(op):
            raise KurtException(f'EvalError: symbol `{op}` has been already used in a formula, declaring it now would change what that formula means')
        if self.is_operator(op) and not self.is_infix(op):    # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol `{op}` already exist as {self._find_symbol(op)}')
        self.check_bool_sig_max(op, 1)
        self.prefix[op] = rbp
        self.nud[op] = lambda ts, kb, op_token: [op_token, parse_expression(ts, kb, rbp)]

    def add_infix(self, op: str, lbp: int, rbp: int) -> None:
        if self.is_used(op):
            raise KurtException(f'EvalError: symbol `{op}` has been already used in a formula, declaring it now would change what that formula means')
        if self.is_operator(op) and not self.is_prefix(op):   # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol `{op}` already exist as {self._find_symbol(op)}')
        self.check_bool_sig_max(op, 2)
        self.infix[op] = (lbp, rbp)                           # to nicely list all operators
        self.led[op] = lambda ts, kb, left, op_token: chain_relations(kb, left, op_token, parse_expression(ts, kb, rbp))
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_postfix(self, op: str, lbp: int) -> None:
        if self.is_used(op):
            raise KurtException(f'EvalError: symbol `{op}` has been already used in a formula, declaring it now would change what that formula means')
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
        if self.is_infix(fun) and not self.is_prefix(fun):
            # an infix binder, e.g. set.kurt's `|` in `{ $z ∈ $A | P $z }`: its left operand is
            # the condition with the bound variable, its right operand the body
            self.bindop.add(fun)
            return
        if self.is_operator(fun):
            raise KurtException(f'EvalError: symbol `{fun}` is already used as prefix, postfix, infix, or bracket')
        if not self.is_arity_set(fun):
            raise KurtException(f'EvalError: before declaring symbol `{fun}` as variable binding, you must set its arity')
        if self.get_arity(fun) < 2:
            raise KurtException(f'EvalError: arity of binding operators must be at least 2')
        self.bindop.add(fun)
        self.nud[fun] = lambda ts, kb, t: bindop_nud(ts, kb, t)   # (defined further below)

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
        if self.is_used(op):
            raise KurtException(f'EvalError: operator `{op}` has been already used in a formula, declaring it "flat" now would change what that formula means')
        if self.is_flat(op):
            raise KurtException(f'EvalError: operator `{op}` is already declared "flat"')
        self.check_bool_sig_sym_flat(op)
        self.flat.add(op)

    def add_sym(self, op) -> None:
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator `{op}` must be infix operator to declare symmetry')
        if self.is_used(op):
            raise KurtException(f'EvalError: operator `{op}` has been already used in a formula, declaring it "sym" now would change what that formula means')
        if self.is_sym(op):
            raise KurtException(f'EvalError: operator `{op}` is already declared "sym"')
        self.check_bool_sig_sym_flat(op)
        self.sym.add(op)

    def get_infix_rbp(self, op: str) -> int:
        # `self.infix[op]` is written once by `add_infix` and never read back during ordinary
        # parsing (the right binding power is baked directly into the `led` closure it
        # creates) -- `bindop_nud` needs it back for a condition's right-hand side, searching
        # the parent levels the same way `get_led`/`get_lbp` do
        if op in self.infix:
            return self.infix[op][1]
        assert self.parent is not None, f'BUG: get_infix_rbp called for non-infix operator `{op}`'
        return self.parent.get_infix_rbp(op)

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
            if ts.peek.value == rbracket:
                # empty body, e.g. `f()` -- see `is_empty_bracket_node`/`process_arity`,
                # which is what turns this into "exactly `f`" for an arity-0 `f`
                token = next(ts)
                token.value = f'{lbracket}$$${rbracket}'
                return [token]
            if lbracket == '(' and isinstance(ts.peek.value, str) and kb.is_operator(ts.peek.value):
                # an operator alone in round brackets is the operator itself, as a term: `(+)`,
                # e.g. `group(ℝ, (+), 0, (-))` -- while `(- x)` is still `- x`
                op_token = next(ts)
                if ts.peek.value == rbracket:
                    next(ts)
                    return op_token
                ts.prepend(op_token)
            suspended = space_suspended[0]
            space_suspended[0] = False           # inside brackets, `f x` is application again
            try:
                expr: Expr = parse_expression(ts, kb, bracket_rbp)
            finally:
                space_suspended[0] = suspended
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
            raise KurtException(f'EvalError: symbol `{s}` is already a variable or starts with `$` or `%`')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol `{s}` is already a constant')
        # (found in the soundness review of 2026-09-29: `alias Q $x`, and cycles `alias q r`, `alias r q`)
        if self.is_var(t) or self.is_fixed_var(t):
            raise KurtException(f'EvalError: an alias is another name for a symbol, not for the variable `{t}`')
        t = self.get_alias(t) or t    # another name for an alias is one for its symbol
        if t == s:
            raise KurtException(f'EvalError: `alias {s}` would make `{s}` another name for itself')
        self.alias[s] = t         # add a key `s` with value `t`

    def add_bool(self, s: str, v: list[int]) -> None:
        if self.is_used(s):
            raise KurtException(f'EvalError: symbol `{s}` has been already used in a formula')
        if len(self.bool_sig(s)) > 0:
            raise KurtException(f'EvalError: symbol `{s}` is already declared bool')
        if self.is_bindop(s) and 1 in v:
            raise KurtException(f'EvalError: first position of binding operator `{s}` can not be declared boolean')
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
        if space_suspended[0]:
            return 0                 # inside a quantifier's condition, see `bindop_nud`
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
        if self.parent is not None:
            yield from self.parent.all_theory()

    def theory_str(self, op:Optional[str]=None, keyword:Optional[str]=None) -> str:
        # the formulas level by level, levels without any are left out
        s: str = self.parent.theory_str(op=op, keyword=keyword) if self.parent is not None else ''
        lines: list[str] = []
        for f in self.theory:
            if op is None or is_op_expr(f.expr, op):
                if keyword is None or f.keyword==keyword:
                    if self.verbose:
                        lines.append(f'{f.formula_str(self)}   {f.simplified_expr}')
                    else:
                        lines.append(f'{f.formula_str(self)}')
        if len(lines) > 0:
            s += f'; on level {self.level}\n' + ''.join(line + '\n' for line in lines)
        return s

    # add new symbols and also add them to the list of symbols that are used in formulas
    # we ignore all bound vars, since they are temporary

    def add_new_symbols(self, e: Expr) -> None:
        for sym in undeclared_symbols(e, self):
            if sym not in new_symbols:
                new_symbols.append(sym)   # noted (or, with `--strict`, rejected) in `scan_parse_check_eval`
        self._add_new_bools(e, True)
        self._add_new_symbols(e, None)

    def _add_new_symbols(self, e: Expr, bound_vars: set[str]|None = None) -> None:
        if bound_vars is None:
            bound_vars = set()
        match e:
            case Token(label='SYMBOL', value=s):
                assert isinstance(s, str), f'BUG: token value must be string`'
                if self.is_var(s) or self.is_const(s):
                    pass
                elif not self.is_used(s):
                    if s not in bound_vars:
                        # if s contains '$$$' (it is from brackets) do not add it as a new constant
                        if '$$$' not in s:
                            self.add_const(s)     # 1. add a new constant if it is not a bound var
                        self.used.add(s)      # 2. add it to the used symbols
            case [*children]:
                match children:
                    case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and self.is_bindop(op):
                        bound_v, _ = unpack_condition(cond, self)
                        bound_vars = bound_vars | {bound_v}   # add v to a copy of `bound_vars`
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
                                    if i == 0 and self.is_bindop(op):
                                        bool_sigs |= _get_new_bool_sigs(args[i], False)   # a binder's variable, or its condition
                                    elif bool_expr(args[i], self):
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
                    return bool_sigs

            return {}

        bool_sig = _get_new_bool_sigs(e, bool_pos)
        for s in bool_sig:
            self.add_bool(s, bool_sig[s])

    def theory_append(self, f: Formula, symbol_level_prev: bool = False) -> None:
        if symbol_level_prev:
            # add the symbols to the previous level
            assert self.parent is not None, f'BUG: can not add symbols one level up, check `assume` implementation'
            self.parent.add_new_symbols(f.expr)
        else:
            self.add_new_symbols(f.expr)
        f.simplified_expr, _ = remove_outer_forall_quantifiers(f.simplified_expr, self)
        f.simplified_expr = rename_all_vars(f.simplified_expr, self)
        dependent_vars.update(find_dependent_vars(f.simplified_expr, self))
        self.theory.append(f)

    def show_append(self, f: Formula) -> None:
        self.add_new_symbols(f.expr)
        f.simplified_expr, _ = remove_outer_forall_quantifiers(f.simplified_expr, self)
        f.simplified_expr = rename_all_vars(f.simplified_expr, self)
        dependent_vars.update(find_dependent_vars(f.simplified_expr, self))
        self.show.append(f)

    def show_str(self) -> str:
        s: str = self.parent.show_str() if self.parent is not None else ''
        if len(self.show) > 0:
            s += f'; on level {self.level}\n' + ''.join(f'{f.formula_str(self)}\n' for f in self.show)
        return s

# create initial knowledge base and define some important constant for the parser
initial_kb: KnowledgeBase = KnowledgeBase(parent=None, mode=('root', []))
begin_rbp:    int = 0                                      # right binding power of beginning of input line
end_lbp:      int = 0                                      # left  binding power of end of input line
bracket_rbp:  int = 1                                      # right binding power of left brackets
bracket_lbp:  int = 1                                      # left  binding power of right brackets
initial_kb.add_brackets('(', ')')                          # round brackets for grouping
string_lbp:   int = 2                                      # left  binding power of strings

def local_led(ts: PeekableGenerator, kb: KnowledgeBase, left: Expr, op_token: Token) -> Expr:
    # `local` immediately precedes the label string it modifies, e.g. `%A implies %A local
    # "restatement"` -- grab that string directly, exactly like `qed`/`with` grab their own
    # expected next token, rather than recursing through `parse_expression` for it
    string_token = next(ts)
    if string_token.label != 'STRING':
        raise KurtException(f'SyntaxError: `{LOCAL_SYMBOL}` must be immediately followed by a string label', string_token.column)
    return [op_token, string_token, left]

initial_kb.lbp[LOCAL_SYMBOL] = string_lbp                  # `local` binds as loosely as a label itself
initial_kb.led[LOCAL_SYMBOL] = local_led
initial_kb.add_infix (COMMA_SYMBOL, 5, 4)                  # comma   is infix operator, right-associative: `(a, b, c)` is the pair `(a, (b, c))`
initial_kb.add_infix (IMPL_SYMBOL, 13, 12)                 # implies is infix operator
initial_kb.add_infix (AND_SYMBOL, 16, 16)                  # and     is infix operator
space_lbp:    int = 90                                     # left  binding power: function application binds most tightly, `f x + y` is `(f x) + y`
space_rbp:    int = 90                                     # right binding power, see `space_lbp`
initial_kb.add_infix (SPACE_SYMBOL, space_lbp, space_rbp)  # space op is for fn like `f x`

initial_kb.add_bool  (TRUE_SYMBOL, [0])                    # true is bool
initial_kb.add_bool  (IMPL_SYMBOL, [0, 1, 2])              # implies is bool with bool input
initial_kb.add_bool  (AND_SYMBOL,  [0, 1, 2])              # and is bool with bool inputs
initial_kb.add_const (TRUE_SYMBOL)                         # true is const symbol
initial_kb.add_const (IMPL_SYMBOL)                         # implies is const symbol
initial_kb.add_const (AND_SYMBOL)                          # and is const symbol
initial_kb.add_flat  (AND_SYMBOL)                          # and is flat
initial_kb.add_sym   (AND_SYMBOL)                          # and is symmetric
initial_kb.add_arity (SUB_SYMBOL, 3)                       # sub takes three args
initial_kb.add_bindop(SUB_SYMBOL)                          # sub is a binding operator
initial_kb.used.add(SUB_SYMBOL)                            # sub can be boolean or non-boolean
initial_kb.add_alias('⊤', TRUE_SYMBOL)                     # alias for true
initial_kb.add_alias('⇒', IMPL_SYMBOL)                     # alias for implies
initial_kb.add_alias('∧', AND_SYMBOL)                      # alias for implies

# `forall`/`exists`' *syntax* (not their axioms -- those stay in `logic.kurt`, exactly like
# `and`-elim stays in `prop.kurt` while `and`'s syntax and `and-intro` are hardcoded above)
# is hardcoded here too, and not just for consistency: `theory_append`/`show_append` (every
# formula ever stored) and `all_theory()` (every derivation search) already unconditionally
# special-case any expression headed by the literal symbol `forall`, via
# `remove_outer_forall_quantifiers` -- regardless of whether any theory has declared it a
# `bindop`. Leaving `forall` undeclared didn't just make `let`'s forall-intro confusing if you
# forgot `load logic`; it meant using the bare word `forall` for *anything* (it parsed as an
# ordinary, flatly space-applied symbol) crashed the very first `theory_append` that saw it,
# since that code assumes the 3-element shape only a real `bindop` parse produces. Declaring it
# here for real removes that landmine outright, rather than merely detecting it more gracefully.
initial_kb.add_arity (FORALL_SYMBOL, 2)                    # forall takes a bound var + a body
initial_kb.add_arity (EXISTS_SYMBOL, 2)                    # exists takes a bound var + a body
initial_kb.add_bindop(FORALL_SYMBOL)                       # forall is a binding operator
initial_kb.add_bindop(EXISTS_SYMBOL)                       # exists is a binding operator
initial_kb.add_bool  (FORALL_SYMBOL, [0, 2])               # forall is bool, its body must be bool
initial_kb.add_bool  (EXISTS_SYMBOL, [0, 2])               # exists is bool, its body must be bool
initial_kb.add_const (FORALL_SYMBOL)                       # forall is const (like true/implies/and above --
initial_kb.add_const (EXISTS_SYMBOL)                       # exists is const  not `.used`-only like `sub`: a
                                                            # `def`'s RHS scan (`extract_by_condition`, no
                                                            # bindop-awareness) or any other "is this symbol
                                                            # already classified" check must recognize forall/
                                                            # exists as already-settled vocabulary; `sub` gets
                                                            # away without this only because it's essentially
                                                            # never written out literally in ordinary formulas
initial_kb.add_alias('∀', FORALL_SYMBOL)                   # alias for forall
initial_kb.add_alias('∃', EXISTS_SYMBOL)                   # alias for exists
initial_kb.frozen = initial_kb.declared_symbols()          # the core can't be changed, e.g. by `sym implies`
core_kb: KnowledgeBase = copy.deepcopy(initial_kb)         # the core only: every file is checked on a copy of it (`load_file`)

################
## kurt lexer ##
################

## expressions
# an expression is either a token or a list of expressions
# instead of creating a class for expressions, we use the following functions

def expr_str(expr: Expr, kb: KnowledgeBase) -> str:
    if kb.format == 'sexpr':
        return expr_sexpr(expr, kb)
    elif kb.format in ['normal', 'original']:
        s: str = expr_normal(expr, kb)
        if len(s) > 0  and  s[0] == '(' and s[-1] == ')':
            s = s[1:-1]         # the brackets are useful during construction, but on the top level we have to omit them
        return s
    else:
        assert False, f'BUG: unknown expression format, got {kb.format}'

def expr_sexpr(expr: Expr, kb: KnowledgeBase) -> str:                      # create s-expression
    match expr:
        case Token(label='STRING', value=v):
            return f'"{v}"'       # quotation marks
        case Token(value=v, origin=origin):
            if origin is None:
                return number_str(v) if isinstance(v, Fraction) else str(v)
            else:
                return str(origin)
        case [Token(label='SYMBOL', value=a), *tail] if isinstance(a, str) and kb.is_bracket_placeholder(a):
            left, right = a.split('$$$')                  # e.g. `{$$$}` -> show as `{}`, not the internal placeholder
            return f'({left}{right} {" ".join([expr_sexpr(e, kb) for e in tail])})'
        case [*entries]:
            return f'({" ".join([expr_sexpr(e, kb) for e in entries])})'
    assert False, f'BUG: unknown expression, got {expr_str(expr, kb)}'

def expr_normal(expr: Expr, kb: KnowledgeBase, rbp: int=0) -> str:          # create raw input expression
    match expr:
        case Token(label='SYMBOL', value=a) if isinstance(a, str) and kb.is_operator(a):
            return f'({a})'                        # an operator as a term, e.g. in `group(G, (+), 0, (-))`
        case Token(label='INT' | 'FLOAT', value=v) if not isinstance(v, str) and v < 0:
            return f'({expr_sexpr(expr, kb)})'     # `P (-1)`, not `P -1`, which reads as `P - 1`
        case Token():
            return expr_sexpr(expr, kb)            # reuse implementation from expr_sexpr
        case [e0]:
            return expr_normal(e0, kb)
        case [Token(label='SYMBOL', value=a), e1] if isinstance(a, str) and kb.is_prefix(a):
            return f'({expr_sexpr(expr[0], kb)} {expr_normal(e1, kb)})'
        case [Token(label='SYMBOL', value=a), e1] if isinstance(a, str) and kb.is_postfix(a):
            return f'({expr_normal(e1, kb)} {expr_sexpr(expr[0], kb)})'
        case [Token(label='SYMBOL', value=a), e1, e2] if isinstance(a, str) and kb.is_infix(a):
            return f'({expr_normal(e1, kb)} {expr_sexpr(expr[0], kb)} {expr_normal(e2, kb)})'
        case [Token(label='SYMBOL', value=a), *tail] if isinstance(a, str) and kb.is_bracket_placeholder(a):
            # split `a` into `left` + `$$$` + `right`
            parts = a.split('$$$')
            assert len(parts) == 2, f'BUG: bracket placeholder must contain `$$$`'
            left, right = parts
            return f'{left} {" ".join([expr_normal(e, kb) for e in tail])} {right}'
        case [Token(label='SYMBOL', value=a), *tail] if isinstance(a, str) and kb.is_flat(a):
            return f'({f" {expr_sexpr(expr[0], kb)} ".join([expr_normal(e, kb) for e in tail])})'
        case [e0, e1]:
            # a plain (arity-processed) function call, e.g. `f a` -- must be parenthesized just
            # like every other node shape above, not left bare: unlike an infix/prefix/postfix
            # node, a bare call has no operator token of its own to anchor precedence when it's
            # nested as an operand of a tighter-binding infix operator (e.g. `f a ∈ B` re-parses
            # as `f (a ∈ B)` if printed without parens around `f a`, since juxtaposition binds
            # looser than most infix operators -- see doc/kurt-doc.md and the `save`/`parse`
            # round-trip regression tests). `expr_str`'s own top-level unwrap already strips this
            # exact pair of parens back off again when the call is printed on its own.
            return f'({expr_normal(e0, kb)} {expr_normal(e1, kb)})'
        case [Token(label='SYMBOL', value=a), e1, e2]:
            return f'({expr_sexpr(expr[0], kb)} {expr_normal(e1, kb)} {expr_normal(e2, kb)})'
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

def equal_expr(t1: Expr, t2: Expr, kb: 'KnowledgeBase', keep_order: bool = True) -> bool:   # equality for expressions
    # note: we assume that `flatness` and `symmetry` has been used to create normalized form
    #
    # alpha-equivalence-aware: two bound variables in corresponding positions (under a
    # shared history of matched binders within t1/t2) count as equal even if spelled
    # differently -- necessary since `rename_all_vars` renames every bound variable to a
    # fresh internal name independently per stored formula (see doc/kurt-soundness.md
    # #3.3), so comparing a *stored* formula's bound-variable names against a freshly
    # user-typed expression's own (different) names must not fail just because of that
    # unrelated renaming. Only the bound-variable *name* tokens themselves get this
    # leniency -- constants, schema variables, and operators still have to match
    # literally, so this can never make two genuinely different formulas compare equal.
    # With `keep_order=False`, also the arguments of `=` and `iff` count in either order
    # (they are `sym`, but keep their order for `def`, see `SYM_KEEP_ORDER`) -- for the kernel.
    return equal_expr_alpha(t1, t2, kb, {}, {}, keep_order)

def equal_expr_alpha(t1: Expr, t2: Expr, kb: 'KnowledgeBase', bmap1: dict, bmap2: dict, keep_order: bool = True) -> bool:
    match (t1, t2):
        case (Token(label=l1, value=v1), Token(label=l2, value=v2)):
            if l1 != l2:
                return False
            if isinstance(v1, str) and isinstance(v2, str) and v1 in bmap1 and v2 in bmap2:
                return bmap1[v1] == v2 and bmap2[v2] == v1     # consistent bound-var correspondence
            if v1 in bmap1 or v2 in bmap2:
                return False    # one side is a bound-variable occurrence, the other isn't
            return v1 == v2
        case ([Token(label='SYMBOL', value=op1), cond1, *tail1], [Token(label='SYMBOL', value=op2), cond2, *tail2]) \
                if isinstance(op1, str) and isinstance(op2, str) and op1 == op2 \
                and kb.is_bindop(op1) and len(tail1) == len(tail2):
            bv1, c1 = unpack_condition(cond1, kb)
            bv2, c2 = unpack_condition(cond2, kb)
            if (c1 is None) != (c2 is None):
                return False
            new_bmap1 = {**bmap1, bv1: bv2}
            new_bmap2 = {**bmap2, bv2: bv1}
            if c1 is not None and not equal_expr_alpha(c1, c2, kb, new_bmap1, new_bmap2, keep_order):
                return False
            return all(equal_expr_alpha(a, b, kb, new_bmap1, new_bmap2, keep_order) for a, b in zip(tail1, tail2))
        case ([Token(label='SYMBOL', value=op1) as head1, *args1], [Token(label='SYMBOL', value=op2) as head2, *args2]) \
                if isinstance(op1, str) and op1 == op2 and len(args1) == len(args2) and len(args1) > 1 \
                and kb.is_sym(op1) and (op1 not in SYM_KEEP_ORDER or not keep_order):
            # the arguments of a symmetric operator are compared as a multiset: their sorted order
            # depends on the names of bound variables, which differ between alpha-equivalent terms
            if not equal_expr_alpha(head1, head2, kb, bmap1, bmap2, keep_order):
                return False
            unused = list(args2)
            for a in args1:
                for i, b in enumerate(unused):
                    if equal_expr_alpha(a, b, kb, bmap1, bmap2, keep_order):
                        del unused[i]
                        break
                else:
                    return False
            return True
        case ([*children1], [*children2]) if len(children1) == len(children2):
            return all(equal_expr_alpha(a, b, kb, bmap1, bmap2, keep_order) for a, b in zip(children1, children2))
        case _:
            return False

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
  (?P<SYMBOL>  [$%]?[A-Za-z][A-Za-z0-9]*          | # symbols 1: identifiers with at most one leading '$' or '%'
               [(){{}}\[\]]                       | # symbols 2: round/curly/square brackets -- always single char, never
                                                     # merge with each other or with symbols 4 (custom `brackets X Y`
                                                     # pairs need this: adjacent punctuation like three dots must not
                                                     # merge into and swallow a following close-bracket character)
               [,]                                | # symbols 3: comma
               [.:=+\-*/#&^'∈!<>|_]+              | # symbols 4: standard operators (greedy multi-char)
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
            yield Token(label, value, column, origin)
        elif label in ('INT', 'FLOAT'):
            assert isinstance(value, str)
            if len(value) > MAX_NUMBER_DIGITS:
                raise KurtException(f'SyntaxError: a number with more than {MAX_NUMBER_DIGITS} digits', column)
            number = Fraction(value)                         # exact: `0.1` is 1/10
            if number.denominator == 1:
                yield Token('INT', int(number), column)      # `1.0` is the number `1`
            else:
                yield Token(label, number, column)
        elif label == 'STRING':
            assert isinstance(value, str)
            yield Token(label, value[1:-1], column)
        elif label == 'NEWLINE': 
            assert False, f'BUG: newlines not allowed in "input_line"'
        elif label == 'LOAD':
            body = match.group('LOAD_BODY')
            yield Token('SYMBOL', 'load', column)
            names = split_filenames(body)
            for i, name in enumerate(names):
                yield Token('STRING', name, column + 5)
                if i < len(names) - 1:
                    yield Token('SYMBOL', COMMA_SYMBOL, column + 5 + len(name))
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
        if op == LOCAL_SYMBOL:
            return True               # `local` immediately before a label, see `local_led`
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

def is_relation(op: Value, kb: KnowledgeBase) -> bool:
    # an infix operator with a boolean result whose arguments are not declared boolean,
    # e.g. `=`, `≠`, `<`, `<=`, `in` -- but not `and`, `implies`, `iff`
    return isinstance(op, str) and kb.is_infix(op) and kb.bool_sig(op) == [0]

# symbols used without being declared first, collected by `add_new_symbols`
new_symbols: list[str] = []

def undeclared_symbols(expr: Expr, kb: KnowledgeBase, bound_vars: frozenset[str] = frozenset()) -> list[str]:
    # the symbols in `expr` that are neither declared nor used before (so, e.g., not `$x`,
    # a bound variable, or a symbol declared with `bool`), in order of appearance
    found: list[str] = []
    def walk(e: Expr, bound: frozenset[str]) -> None:
        match e:
            case Token(label='SYMBOL', value=v) if isinstance(v, str):
                if (v not in bound and v[0] not in '$%' and '$$$' not in v and v not in found
                        and not kb.is_used(v) and not kb.is_declared(v)):
                    found.append(v)
            case [Token(label='SYMBOL', value=op), cond, *_] if isinstance(op, str) and kb.is_bindop(op):
                bv, _ = unpack_condition(cond, kb)
                for child in e:
                    walk(child, bound | {bv})
            case [*children]:
                for child in children:
                    walk(child, bound)
    walk(expr, bound_vars)
    return found

# whether function application is switched off while parsing, see `bindop_nud`
space_suspended: list[bool] = [False]

def bindop_nud(ts: PeekableGenerator, kb: KnowledgeBase, t: Token) -> Expr:
    # a binding operator with a condition, e.g. `∀ $n ∈ Nat P $n` or `∃ $d > 0 ...`: since
    # function application binds most tightly, the condition `$n ∈ Nat` is read here, with the
    # right-hand side extending over infix operators but not over an application -- so the body
    # `P $n` stays outside of it (`∀ ($n ∈ Nat) (P $n)` with brackets works as well)
    v = ts.peek
    if not (isinstance(v, Token) and v.label == 'SYMBOL' and isinstance(v.value, str) and not kb.is_operator(v.value)):
        return t
    next(ts)
    op = ts.peek
    if not (isinstance(op, Token) and op.label == 'SYMBOL' and is_relation(op.value, kb)):
        ts.prepend(v)
        return t
    next(ts)
    suspended = space_suspended[0]
    space_suspended[0] = True
    try:
        rhs = parse_expression(ts, kb, kb.get_infix_rbp(op.value))
    finally:
        space_suspended[0] = suspended
    return [space_token, t, [op, v, rhs]]

def chain_relations(kb: KnowledgeBase, left: Expr, op_token: Token, right: Expr) -> Expr:
    # mathematicians write `a = b <= c` for `a = b and b <= c`: an infix relation whose (not
    # parenthesized) left operand is itself a relation (or such a chain) becomes a conjunction,
    # reusing the middle term, e.g. `a = b <= c < d` is `a = b and b <= c and c < d`.  Without
    # this, `a = b <= c` would parse as `(a = b) <= c`; parentheses still give that reading.
    if not is_relation(op_token.value, kb) or not isinstance(left, list) or len(left) < 3:
        return [op_token, left, right]
    head = left[0]
    if not isinstance(head, Token) or head.label != 'SYMBOL':
        return [op_token, left, right]
    if head.value == AND_SYMBOL and head.chained:
        last = left[-1]                        # continue an existing chain
        assert isinstance(last, list) and len(last) == 3
        return left + [[op_token, deepcopy_expr(last[2]), right]]
    if is_relation(head.value, kb) and len(left) == 3:
        and_token = Token('SYMBOL', AND_SYMBOL, column=op_token.column, chained=True)
        return [and_token, left, [op_token, deepcopy_expr(left[2]), right]]
    return [op_token, left, right]

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
        is_var = isinstance(val, str) and kb.is_var(val)
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
    ignore = SYM_KEEP_ORDER
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

def flatten_op(flat_op: str, expr: Expr, kb: KnowledgeBase) -> Expr:  # flatten nested 'op'-expressions
    # e.g. [',', 17, [',', 42, 100]] --> [',', 17, 42, 100]
    match expr:
        case [Token(label='SYMBOL', value=op), *tail] if op==flat_op:
            e: Expr = [expr[0]]
            for child in tail:
                ee: Expr = flatten_op(flat_op, child, kb)
                if is_op_expr(ee, flat_op):
                    assert isinstance(ee, list) and len(ee) > 1
                    e.extend(ee[1:])
                else:
                    e.append(ee)
            return e
        case [*_]:
            return [flatten_op(flat_op, e, kb) for e in expr]
        case Token():
            return expr
    assert False, f'BUG: expression must be list or Token, got {expr_str(expr, kb)}'

def flatten_all(expr: Expr, kb: KnowledgeBase) -> Expr:
    for op in kb.all_flat():
        expr = flatten_op(op, expr, kb)       # flatten certain operators
    return expr

def is_empty_bracket_node(e: Expr, kb: KnowledgeBase) -> bool:
    # `()`/`{}`/etc. parsed with nothing inside -- see `add_brackets`'s `nud`. Used by
    # `group_by_arity`/`process_arity` to give `f()` a meaning: exactly `f` for an arity-0
    # `f` (see `todo.md`'s own spec: "`f()` ... should be parsed [like] just `f`"), and a
    # clear rejection rather than a confusing parse for a positive-arity `f`.
    return (isinstance(e, list) and len(e) == 1 and isinstance(e[0], Token)
            and isinstance(e[0].value, str) and kb.is_bracket_placeholder(e[0].value))

def spread_arguments(op: str, arity: int, tail: list[Expr], kb: KnowledgeBase) -> Optional[list[Expr]]:
    # `g(a, b)` for a `g` of arity 2 means `g a b`: a comma list in round brackets gives the
    # arguments -- but only where `g` wouldn't get enough arguments otherwise, so `g (a, b) c`
    # stays `g` applied to the pair `(a, b)` and to `c`; binders (`sum`, ...) take their arguments
    # as they are
    if arity < 2 or kb.is_bindop(op) or len(tail) >= arity:
        return None
    match tail[0]:
        case [Token(label='SYMBOL', value='($$$)'), [Token(label='SYMBOL', value=c), *_] as inner] if c == COMMA_SYMBOL:
            args = flatten_op(COMMA_SYMBOL, inner, kb)
            assert isinstance(args, list)
            args = args[1:]
            if len(args) != arity:
                raise KurtException(f'EvalError: `{op}` takes {arity} arguments, got {len(args)} in `({", ".join(expr_str(a, kb) for a in args)})`')
            return args
    return None

def group_by_arity(expr: Expr, kb: KnowledgeBase) -> tuple[Expr, list[Expr]]:
    # input: `expr` which is a list of functions and arguments
    # output: `e` which is properly group and the `tail` which is the rest of non-eaten arguments
    match expr:
        case [Token(label='SYMBOL', value=op), *tail] if isinstance(op, str) and ((arity:=kb.get_arity(op)) > 0):
            e: Expr = [expr[0]]                                       # the new expression
            spread = spread_arguments(op, arity, tail, kb)
            if spread is not None:
                return [expr[0], *spread], tail[1:]
            for i in range(1, arity+1):
                if len(tail) == 0:
                    raise KurtException(f'EvalError: not enough arguments for `{op}`')
                ei: Expr
                tail: list[Expr]
                ei, tail = group_by_arity(tail, kb)             # let the next one eat as many expr as it needs
                if is_empty_bracket_node(ei, kb):
                    empty = str(ei[0].value).replace('$$$', '') if isinstance(ei, list) and isinstance(ei[0], Token) else '()'
                    raise KurtException(f'EvalError: empty brackets `{empty}` cannot supply an argument for `{op}`, which needs {arity} argument(s)')
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
        case [Token(label='SYMBOL', value=v), Token(label='SYMBOL', value=head) as head_token, *_] if v==SPACE_SYMBOL \
                and isinstance(head, str) and kb.is_operator(head) and not kb.is_var(head):
            # `(implies)` is the operator as a term (e.g. an argument of `group`), not a function
            raise KurtException(f'ParseError: the operator `({head})` in parentheses is a term, it can not be applied to arguments -- write it as an operator, like `A {head} B`', head_token.column)
        case [Token(label='SYMBOL', value=v), *tail] if v==SPACE_SYMBOL:
            expr, tail = group_by_arity(tail, kb)
            # `f()` for arity-0 `f` means exactly `f` -- drop a leading empty-parens marker
            # rather than wrapping it into a call, so `f()` and `f` parse identically
            if (len(tail) > 0 and is_empty_bracket_node(tail[0], kb)
                    and isinstance(expr, Token) and isinstance(expr.value, str) and kb.get_arity(expr.value) == 0):
                tail = tail[1:]
                if len(tail) == 0:
                    return expr              # `f()` alone parses to exactly `f`, nothing to recurse into
            if len(tail) > 0:
                expr = [expr] + tail         # extra arguments (might be there for keywords!)
    assert isinstance(expr, list)
    return [process_arity(e, kb) for e in expr]

def remove_round_brackets(expr: Expr, kb: KnowledgeBase) -> Expr:
    match expr:
        case Token():
            return expr
        case [Token(label='SYMBOL', value='($$$)') as t]:
            # (`f()` for an arity-0 `f` is already `f`, see `process_arity`)
            raise KurtException(f'ParseError: empty parentheses `()` stand for nothing here', t.column)
        case [Token(label='SYMBOL', value='($$$)'), sub_expr]:
            return remove_round_brackets(sub_expr, kb)
        case [*list_expr]:
            return [remove_round_brackets(e, kb) for e in list_expr]
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

def check_expr_label(expr: Expr, kb) -> tuple[Expr, str, bool]:      # check [expr] [local] [label]
    # cases:
    #   x=9  "eq 1"
    #   x=9  local "eq 1"       -- see `local_led`: not exported when this file is `load`ed
    #   true
    #   x=9
    label = ''
    local = False
    match expr:
        case [Token(label='SYMBOL', value=v), Token(label='STRING', value=label), tail] if v == LOCAL_SYMBOL:
            assert isinstance(label, str)
            local = True
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
    return tail, label, local

def post_process(kb: KnowledgeBase, expr: Expr) -> tuple[Expr, str, bool]:
    expr = flatten_op(SPACE_SYMBOL, expr, kb)           # flatten all space operators
    expr = process_arity(expr, kb)                      # turns space operators into function calls according to arities
    expr = remove_round_brackets(expr, kb)              # remove round brackets for grouping
    expr, label, local = check_expr_label(expr, kb)     # check and split `expr`, `label`, and `local`
    expr = flatten_all(expr, kb)                        # flatten `flat` operators
    expr = symmetrize_all(expr, kb)                     # symmetrize `sym` operators
    if kb.calc:
        expr = kb.calculate(expr)
    return expr, label, local

def parse_tokenstream(ts: PeekableGenerator, kb: KnowledgeBase) -> tuple[Optional[Token], list[Expr], str, bool]:
    assert isinstance(ts.peek, Token)
    keyword_token: Optional[Token] = None
    keyword: str = ''
    label: str = ''
    local: bool = False
    if ts.peek.label == 'SYMBOL' and ts.peek.value in keywords:
        keyword = ts.peek.value
        keyword_token = next(ts)                              # remove a keyword right away early
    if ts.peek.label == 'END':
        return keyword_token, [], '', False                   # empty token stream
    expr_list: list[Expr]
    if keyword_token is None or keyword_token.value in keywords_with_parsing:
        expr: Expr  = parse_expression(ts, kb, begin_rbp)     # parse expression
        expr, label, local = post_process(kb, expr)           # turn spaces into calls, symmetry, flatness
        expr_list = chop_off_comma(expr)
        check_for_helper_keywords(expr_list)    # `with` is only allowed on top level
        check_no_keyword(expr_list)             # keywords are not allowed in expressions
        try:
            type_check_expression(expr, kb)                       # (some) type checking
        except KurtException as e:
            if keyword_token is not None and keyword_token.value == 'parse':
                print(f'type check failed: {e.msg}', file=sys.stderr)   # `parse` shows it anyway
            else:
                print(f'parsed as: {expr_str(expr, kb)}', file=sys.stderr)
                raise e      # reraise it
    else:
        expr_list = split_by_comma(list(ts)[:-1])             # [:-1] removes end_token
        check_no_keyword(expr_list)             # don't check the `keyword` and the `label`
    return keyword_token, expr_list, label, local

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

def bare_bool_schema_axiom_warning(expr: Expr, kb: KnowledgeBase) -> Optional[str]:
    # heuristic warning (not a soundness check, see doc/kurt-soundness.md #6): a `%`/`$`
    # schema variable in a `use`/`def` axiom means "for any value of this symbol", so a bare
    # `use %A`, or `use %A implies X` (or `def d iff %A`) where `%A` doesn't reappear on the
    # other side, quietly asserts "every proposition is true" -- since `%A` freely unifies
    # with anything (including `true`), the axiom then makes its conclusion (or, for the
    # bare case, any proposition at all) derivable completely unconditionally. Only catches
    # these few obvious syntactic shapes (after peeling any outer `forall`s, which don't
    # change the effect, see doc/kurt-soundness.md #2.2) -- there's no attempt to catch
    # every equivalent phrasing, since a complete detector would need to decide whether an
    # arbitrary formula is a tautology, not just pattern-match. Never rejects: such an axiom
    # is occasionally written on purpose (much like `use false` is allowed outright).
    while isinstance(expr, list) and len(expr) == 3 and isinstance(expr[0], Token) and expr[0].value == FORALL_SYMBOL:
        expr = expr[2]      # a leading `forall` (over anything) doesn't change this check

    def bare_bool_var(e: Expr) -> Optional[str]:
        if isinstance(e, Token) and e.label == 'SYMBOL' and isinstance(e.value, str) and kb.is_var(e.value) and kb.is_bool(e.value):
            return e.value
        return None

    var = bare_bool_var(expr)
    if var is not None:
        return f'Warning: `{expr_str(expr, kb)}` asserts every proposition is true (a `%`/`$` schema variable in `use` means "for any value"), making anything derivable unconditionally -- see doc/kurt-soundness.md #6'

    if isinstance(expr, list) and len(expr) == 3 and isinstance(expr[0], Token) and isinstance(expr[0].value, str):
        op, lhs, rhs = expr[0].value, expr[1], expr[2]
        if op == IMPL_SYMBOL:
            var = bare_bool_var(lhs)
            if var is not None and not contains(rhs, {var}, kb):
                return f'Warning: `{expr_str(expr, kb)}` is derivable unconditionally -- `{var}` freely unifies with anything and does not reappear in the conclusion -- see doc/kurt-soundness.md #6'
        elif op in (EQUAL_SYMBOL, IFF_SYMBOL):
            for side, other in ((lhs, rhs), (rhs, lhs)):
                var = bare_bool_var(side)
                if var is not None and not contains(other, {var}, kb):
                    return f'Warning: `{expr_str(expr, kb)}` makes `{expr_str(other, kb)}` exactly as unconstrained as `{var}`, so it becomes trivially provable -- see doc/kurt-soundness.md #6'
    return None

def eval_use(kb: KnowledgeBase, expr: Expr, input_line: str,label: str, filename: str, line: int, mainstream: bool, keyword: str, local: bool = False) -> Formula:
    if not bool_expr(expr, kb, strict=False):    # not strict, since we are possibly adding new symbols
        raise KurtException(f'EvalError: must evaluate to boolean, got `{expr_str(expr, kb)}`')
    warning = bare_bool_schema_axiom_warning(expr, kb)
    if warning is not None:
        print(decorate_reason(mainstream, warning, filename, str(line)), file=sys.stderr)
    reason = 'without proof'
    if len(label) > 0:
        reason += f' "{label}"'
    reason = decorate_reason(mainstream, reason, filename, str(line))
    return Formula(kb, expr, input_line, str(line), filename, label, reason, keyword, local=local)

def eval_show(kb: KnowledgeBase, expr: Expr, input_line: str, label: str, filename: str, line: int, mainstream: bool, local: bool = False) -> KnowledgeBase:
    if not bool_expr(expr, kb, strict=False):   # not strict, since we are possibly adding new symbols
        raise KurtException(f'EvalError: must evaluate to boolean, got `{expr_str(expr, kb)}`')
    reason = decorate_reason(mainstream, 'claim', filename, str(line))
    if len(label) > 0:
        reason += f' "{label}"'
    f = Formula(kb, expr, input_line, str(line), filename, label, reason, keyword='show', local=local)
    kb.show_append(f)
    if mainstream:
        log(kb, f'show {expr_str(expr, kb)}', reason, kb.level)
    return kb

def eval_proof(kb: KnowledgeBase, mainstream: bool) -> KnowledgeBase:
    if len(kb.show) == 0:
        raise KurtException(f'ProofError: can not start proof since there is no planned formula on current level')
    if mainstream:
        log(kb, 'proof', '', kb.level)
    kb = kb.push_level('proof', [])          # add a new level/scope to the knowledgebase
    return kb

# def
# LHS: exactly one unused symbol that is not a variable or boolean variable
# `def` is safe only if `=` and `iff` have their usual meaning, so they must come from the
# theories that come with Kurt
DEF_THEORIES = {EQUAL_SYMBOL: 'equality', IFF_SYMBOL: 'prop'}

def is_packaged_theory_loaded(name: str, kb: KnowledgeBase) -> bool:
    candidate = packaged_theory_file(name + '.kurt')
    return candidate is not None and kb.get_load_level(str(candidate)) is not None

def eval_def(kb: KnowledgeBase, expr: Expr, input_line: str, label: str, filename: str, line: int, mainstream: bool, local: bool = False) -> tuple[Formula, str]:
    for op, theory in DEF_THEORIES.items():
        if contains_symbol(expr, op) and not is_packaged_theory_loaded(theory, kb):
            raise KurtException(f'EvalError: `def` with `{op}` needs the theory that gives `{op}` its meaning -- `load {theory}` first')
    match expr:
        case [Token(label='SYMBOL', value=s), LHS, RHS] if isinstance(s, str) and (s== EQUAL_SYMBOL or s==IFF_SYMBOL):
            lhs_candidates = extract_by_condition(LHS, lambda s: not kb.is_const(s) and not kb.is_var(s) and not kb.is_bracket_placeholder(s), kb)
            if len(lhs_candidates) != 1:
                raise KurtException(f'EvalError: `def` requires exactly one new constant on the left-hand side, got `{lhs_candidates}` in `{expr_str(expr, kb)}`')
            lhs_const = lhs_candidates[0]
            rhs_candidates = extract_by_condition(RHS, lambda s: not kb.is_const(s) and not kb.is_var(s) and not kb.is_bracket_placeholder(s), kb)
            if len(rhs_candidates) != 0:
                raise KurtException(f'EvalError: `def` does not allow new symbols on the right-hand side, got `{rhs_candidates}` in `{expr_str(expr, kb)}`')
            # a definition must be conservative, i.e. only give a name to the right-hand side: the
            # left-hand side is the new symbol applied to distinct variables (`c`, `f($x, $y)`,
            # `$a ⊂ $b`), and the right-hand side has no other variables -- otherwise e.g.
            # `def c = $y` gives `c = 1` and `c = 2`, and `def c * 0 = 1` gives `0 = 1`
            def definiendum_vars(e: Expr) -> Optional[list[str]]:
                # the variables of `c`, `c($x, ...)`, or curried, `(c $f $g) $x` -- `None` if `e`
                # is not of that shape
                match e:
                    case Token(label='SYMBOL', value=v) if v == lhs_const:
                        return []
                    case [head, *params] if params and all(is_var_token(p, kb) for p in params):
                        inner = definiendum_vars(head)
                        return None if inner is None else inner + [p.value for p in params]   # type: ignore[union-attr]
                    case [Token(label='SYMBOL', value=op), *params] if (isinstance(op, str)
                            and sum(1 for p in params if isinstance(p, Token) and p.value == lhs_const) == 1
                            and all(is_var_token(p, kb) or (isinstance(p, Token) and p.value == lhs_const) for p in params)
                            and not any(contains_symbol(f.expr, op) for f in kb.all_theory())):
                        # e.g. `$f is injective`: the new symbol as an argument of an operator that
                        # no formula mentions yet, so all instances are new, different terms
                        return [p.value for p in params if is_var_token(p, kb)]   # type: ignore[union-attr]
                return None
            found_vars = definiendum_vars(LHS)
            if found_vars is None:
                raise KurtException(f'EvalError: `def` needs the new `{lhs_const}` applied to variables on the left-hand side, like `{lhs_const}($x, $y)`, got `{expr_str(LHS, kb)}`')
            lhs_vars: list[str] = found_vars
            if len(set(lhs_vars)) != len(lhs_vars):
                raise KurtException(f'EvalError: `def` needs distinct variables on the left-hand side, got `{expr_str(LHS, kb)}`')
            extra = sorted(free_bound_vars(RHS, kb)[0] - set(lhs_vars))
            if extra:
                raise KurtException(f'EvalError: the variables {", ".join(f"`{v}`" for v in extra)} of the right-hand side of `def` must occur on the left-hand side too')
            if kb.is_sym(lhs_const) or kb.is_flat(lhs_const):
                raise KurtException(f'EvalError: `{lhs_const}` is declared `sym` or `flat`, which `def` would have to prove -- define it without')
        case _:
            raise KurtException(f'EvalError: `def` only allowed with `{EQUAL_SYMBOL}` and `{IFF_SYMBOL}`, got `{expr_str(expr, kb)}`')
    f = eval_use(kb, expr, input_line, label, filename, line, keyword='def', mainstream=False, local=local)
    f.def_symbol = lhs_const
    return f, lhs_const

def contains_symbol(expr: Expr, symbol: str) -> bool:
    if isinstance(expr, Token):
        return expr.label == 'SYMBOL' and expr.value == symbol
    return any(contains_symbol(e, symbol) for e in expr)

def contains(expr: Expr, symbols: set[str], kb: KnowledgeBase) -> bool:
    # check whether the `expr` contains certain `symbols`
    # note that bound variables are ignored
    match expr:
        # symbols
        case Token(label='SYMBOL', value=s):
            assert isinstance(s, str)
            return s in symbols
        # binding operator
        case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and kb.is_bindop(op):
            bound_v, condition = unpack_condition(cond, kb)
            symbols_wo_bound_v = symbols - {bound_v}  # set difference creating a new set
            cond_check = False if condition is None else contains(condition, symbols_wo_bound_v, kb)
            return cond_check or contains(tail, symbols_wo_bound_v, kb)
        # other list
        case [*children]:
            return any(contains(c, symbols, kb) for c in children)
        case _:
            return False

def free_symbols(expr: Expr, kb: KnowledgeBase, bound_vars: frozenset[str] = frozenset()) -> set[str]:
    # collect every symbol name occurring free (not bound by an enclosing binder) in `expr`
    # -- used by `merge_and_pop` to compute which symbol declarations an exported fact needs
    # to travel with it when this file is `load`ed elsewhere (see doc/kurt-doc.md's `load`
    # section). Bound-variable-aware, mirroring `contains` above.
    match expr:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and s not in bound_vars:
            return {s}
        case Token():
            return set()
        case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and kb.is_bindop(op):
            bound_v, condition = unpack_condition(cond, kb)
            new_bound_vars = bound_vars | {bound_v}
            found = set() if op in bound_vars else {op}
            if condition is not None:
                found |= free_symbols(condition, kb, new_bound_vars)
            for child in tail:
                found |= free_symbols(child, kb, new_bound_vars)
            return found
        case [*children]:
            found: set[str] = set()
            for child in children:
                found |= free_symbols(child, kb, bound_vars)
            return found
        case _:
            return set()

def eval_done(kb: KnowledgeBase, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    # a DEDENT (or `qed`) is closing a block opened by `assume`, `let`, `pick`, `proof`,
    # `sandbox`, or `expect`, hereby triggering `not-intro`, `forall-intro`, `impl-intro`,
    # `exists-elim`, `qed`'s own check, a silent discard, or an expected-error check

    # (1) for `assume` (not-intro and impl-impl) create new constants already on the level below
    # (2) for `let` (forall-intro) and `pick` (exists-elim) create new constants on the new level

    # try to construct `expr` depending on the mode of the current level
    # these calls might generate exceptions
    if kb.mode_str == 'sandbox':
        # nothing to derive -- a `sandbox` is scratch space, dedenting out of it (like `break`
        # would) just discards everything inside it, no formula is added anywhere
        kb = kb.pop_level()
        if mainstream:
            log(kb, 'sandbox', f'{line} closed, its content is discarded', kb.level)
        return kb
    if kb.mode_str == 'expect':
        assert len(kb.mode_args) == 1 and isinstance(kb.mode_args[0], Token)
        expected_kind = kb.mode_args[0].value
        # deliberately not one of `KurtException.KNOWN_KINDS`, so this can never be
        # mistaken by `read_eval_loop` for the very error it says didn't happen
        raise KurtException(f'ExpectationError: this `expect "{expected_kind}"` block finished without raising a `{expected_kind}`')
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: no formula has been proven, this block can only be closed after a successful proof step')
    if kb.theory[-1].expr == todo_token:
        raise KurtException(f'ProofError: a bare `todo` admits the next step, it can\'t be the last line of a block -- write `todo FORMULA`')
    last_expr = kb.theory[-1].expr
    mode_str = kb.mode_str
    match mode_str:
        case 'assume' | 'case':
            assert len(kb.mode_args) == 1, f'BUG: mode_args for "assume" must have length one, got `{kb.mode_args}`'
            assumption = kb.mode_args[0]
            # impl-intro
            expr = [Token('SYMBOL', IMPL_SYMBOL), assumption, last_expr]
        case 'let':
            # forall-intro
            assert len(kb.mode_args) > 0, f'BUG: mode_args for "fix" must have length > 0, got `{kb.mode_args}`'
            expr = last_expr
            for condition in reversed(kb.mode_args):
                assert kb.parent is not None
                if not is_bool_var_token(condition, kb.parent):
                    expr = [Token('SYMBOL', FORALL_SYMBOL), condition, expr]
        case 'pick':
            # exists-elim
            assert len(kb.mode_args) > 0, f'BUG: mode_args for "pick" must have length > 0, got `{kb.mode_args}`'
            expr = last_expr
            # check that `expr` does not contain any *individual* constants from the current
            # level (the witness itself, or any bystander `const` declared alongside it) --
            # vocabulary symbols first used here are fine, see `is_vocabulary_symbol`
            witness = kb.mode_args[0].value if isinstance(kb.mode_args[0], Token) else None
            pick_not_allowed = set(filter(lambda s: not kb.is_vocabulary_symbol(s), kb.const)) | ({witness} if isinstance(witness, str) else set())
            if contains(expr, pick_not_allowed, kb):
                raise KurtException(f'ProofError: the line (its conclusion) of the `pick` block may not contain constant symbols from the current level, got `{expr_str(expr, kb)}`')
        case 'proof':
            return eval_qed(kb, filename, line, mainstream)
        case 'root':
            raise KurtException(f'ProofError: no block to close, already at the top level')

    # the constants on the current level are not allowed, however, the variables of the previous
    # level are allowed (see `de-morgan.kurt`), and neither are vocabulary symbols that were only
    # registered as "const" here because this happened to be where they were *first used* (see
    # `is_vocabulary_symbol`) -- those don't go out of scope in any meaningful sense: nothing
    # about them depends on this block's fresh constants, and their own syntax declarations
    # (`arity`, `infix`, ...) are discarded when this level is popped regardless (`pop_level`
    # does not merge symbol tables the way `merge_and_pop` does for a `load`), so there is
    # nothing left to leak except the plain symbol name inside the one formula this block is
    # already handing up on purpose. Excluding them fixes false rejections like `bool P; arity P
    # 1; let x / use P x / P x` -- `P` used for the first time inside the block used to be
    # wrongly treated as if it were as scoped as a `let`/`pick`/`const`-introduced individual.
    assert kb.parent is not None, f'BUG: we should be one-level up in `eval_done`'
    kb_parent = kb.parent
    not_allowed = set(filter(lambda s: not kb_parent.is_var(s) and not kb.is_vocabulary_symbol(s), kb.const))
    if contains(expr, not_allowed, kb_parent):
        raise KurtException(f'ProofError: there are constant symbols on the current level appearing in the conclusion of the previous one, got `{expr_str(expr, kb_parent)}`, not allowed are {not_allowed}')

    # every binder of the result must bind the same variable outside the block as inside (the
    # bound variable of a condition like `a < x` depends on which symbols are constants)
    reading_problem = binder_reading_changes(kb, expr, last_expr)
    if reading_problem is not None:
        raise KurtException(f'ProofError: {reading_problem}')

    # the kernel checks the step, with the block's level (see `kernel_verify_block`)
    block = kb
    rule_name = {'assume': 'impl-intro', 'case': 'impl-intro', 'let': 'forall-intro', 'pick': 'exists-elim'}[mode_str]
    reason = record_certificate(Certificate(rule_name, expr, frozenset(), kb.theory[-1], block=block), block).short(filename, mainstream)
    not_reason = ''
    if mode_str == 'assume' and isinstance(last_expr, Token) and last_expr.value == FALSE_SYMBOL:
        not_expr: Expr = [Token('SYMBOL', NOT_SYMBOL), kb.mode_args[0]]
        not_reason = record_certificate(Certificate('not-intro', not_expr, frozenset(), kb.theory[-1], block=block), block).short(filename, mainstream)

    # add a the new formula to the theory
    reason = decorate_reason(mainstream, reason, filename, str(line))
    f = Formula(kb, expr, '', str(line), filename, '', reason, keyword='')
    kb = kb.pop_level()                    # drop current level and perform some checks
    kb.theory_append(f)                    # add a copy to the theory
    if mainstream:
        log(kb, f.formula_str(kb), reason, kb.level)

    # can we infer further with "not-intro"?
    if mode_str == 'assume':
            match last_expr:
                case Token(label='SYMBOL', value=v) if v == FALSE_SYMBOL:
                    # not-intro, some extra formula!
                    expr: Expr = [Token('SYMBOL', NOT_SYMBOL), assumption]
                    reason = not_reason
                    reason = decorate_reason(mainstream, reason, filename, str(line))
                    f = Formula(kb, expr, '', str(line), filename, '', reason, keyword='')
                    kb.theory_append(f)                    # add a copy to the theory
                    if mainstream:
                        log(kb, f.formula_str(kb), reason, kb.level)

    return kb

def binder_reading(e: Expr, kb: KnowledgeBase) -> Optional[list[str]]:
    # the variables bound by the binders of `e`, in order, as read with `kb` -- `None` if a
    # condition can't be read
    match e:
        case Token():
            return []
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            try:
                bv, _ = unpack_condition(cond, kb)
            except KurtException:
                return None
            parts = [binder_reading(c, kb) for c in [cond, *body]]
            return None if any(p is None for p in parts) else [bv] + [v for p in parts for v in p]   # type: ignore[union-attr]
        case [*children]:
            parts = [binder_reading(c, kb) for c in children]
            return None if any(p is None for p in parts) else [v for p in parts for v in p]   # type: ignore[union-attr]
    return None

def binder_reading_changes(block: KnowledgeBase, result: Expr, last: Expr) -> Optional[str]:
    # whether the result of closing `block` reads differently at the parent than its last line
    # did inside the block -- e.g. `let (0 < a)` / `let (a < x)` gives `∀ (0 < a) ∀ (a < x) ...`,
    # where outside, `a` is no constant any more, and `a < x` would bind `a`
    assert block.parent is not None
    parent = block.parent
    inside = binder_reading(last, block)
    outside = binder_reading(result, parent)
    if inside is None or outside is None:
        return None     # can't be read at all -- the other checks report that
    if block.mode_str == 'let':
        prefix = [name for c, name in zip(block.mode_args, block.let_names) if not is_bool_var_token(c, parent)]
    elif block.mode_str in ('assume', 'case'):
        prefix = binder_reading(block.mode_args[0], parent) or []
    else:
        prefix = []
    if outside != prefix + inside:
        return (f'a condition in `{expr_str(result, parent)}` would bind another variable outside the block '
                f'-- write the bound variable on the left of the relation (e.g. `x > a` for `a < x`), or use `∀ x (... ⇒ ...)`')
    return None

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
        reason = decorate_reason(mainstream, 'by todo', filename, str(line))
    else:
        # block all free variables of the planned expression, since they are universally quantified
        blocked_as_domain = frozenset(free_vars_only(planned_expr, kb))
        s = State({}, blocked_as_domain, frozenset())
        certs, _ = derive_expr(planned_expr, filename, mainstream, s, kb)  # this might raise ProofError exceptions
        reason = decorate_reason(mainstream, ', '.join(c.short(filename, mainstream) for c in certs), filename, str(line))
    # carry the `show`'s own label/local marker forward -- a proved, named theorem must stay
    # exportable exactly like a labelled `use`/`def` axiom would be (see doc/kurt-doc.md's
    # `load` section); this used to be silently dropped (`label = ''` unconditionally) here
    f = Formula(kb, planned_f.expr, planned_f.input_line, str(planned_f.line), filename, planned_f.label, reason, keyword='', local=planned_f.local)
    kb = kb.pop_level()                        # drop current level and perform some checks
    kb.show.pop()                              # pop the last planned formula off the show stack, since it is proved now
    kb.theory_append(f)                        # add a copy to the current theory
    if mainstream:
        log(kb, 'qed', reason, kb.level)
    return kb

def is_new_symbol_or_existing_variable(s: str, kb: KnowledgeBase) -> bool:
    # a variable, or a symbol without any declaration (a predicate declared with `bool`/`arity`
    # but not used yet is not a new symbol)
    return kb.is_var(s) or not (kb.is_const(s) or kb.is_operator(s) or kb.is_arity_set(s) or len(kb.bool_sig(s)) > 0 or kb.is_bindop(s))

def extract_by_condition(e: Expr, c: Callable[[str], bool], kb: KnowledgeBase, bound_vars: frozenset[str] = frozenset()) -> list[str]:
    # bound-variable-aware: a symbol only bound by an enclosing binder (e.g. the `x` in
    # `forall x (...)`) is scoped to that binder and must never be reported as a free
    # "new symbol", regardless of whether it happens to satisfy `c` -- mirrors `contains`'s
    # own bound-variable exclusion above.
    match e:
        case Token(label='SYMBOL', value=s) if isinstance(s, str) and s not in bound_vars and c(s):
            return [s]        # new string fulfilling the condition
        case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and kb.is_bindop(op):
            bound_v, condition = unpack_condition(cond, kb)
            new_bound_vars = bound_vars | {bound_v}
            found = [] if condition is None else extract_by_condition(condition, c, kb, new_bound_vars)
            for child in tail:
                found += extract_by_condition(child, c, kb, new_bound_vars)
            return found
        case [*children]:
            found = []
            for child in children:
                found += extract_by_condition(child, c, kb, bound_vars)
            return found
    return []

# what is allowed for `let`?
#     let x      ; x must be new constant or existing variable
#     let x>0    ; x must be new constant or existing variable
def unpack_condition(expr: Expr, kb: KnowledgeBase) -> tuple[str, Optional[Expr]]:
    if isinstance(expr, Token):
        if expr.label != 'SYMBOL':
            raise KurtException(f'EvalError: expected a symbol, got `{expr_str(expr, kb)}`', expr.column)
        assert isinstance(expr.value, str)
        new_const = expr.value
        condition = None
    elif is_sub(expr):
        # a rule's binder with *any* condition, e.g. `∀ (sub $x $v %C) %P`: the bound variable
        # is `$v`, and the condition is `%C` with `$v` in the hole `$x` (see `sub_condition_match`)
        assert isinstance(expr, list)
        v = expr[2]
        if not (isinstance(v, Token) and v.label == 'SYMBOL' and isinstance(v.value, str) and kb.is_var(v.value) and not kb.is_bool(v.value)):
            raise KurtException(f'EvalError: in the condition `{expr_str(expr, kb)}` of a binder, the value of `{SUB_SYMBOL}` must be the bound variable')
        new_const = v.value
        condition = expr
    else:
        # distinct names: the variable may occur more than once, e.g. `$x > 0 ∧ $x < 1`
        new_consts = list(dict.fromkeys(extract_by_condition(expr, lambda s: is_new_symbol_or_existing_variable(s, kb), kb)))
        if len(new_consts) > 1:
            # several, e.g. `$a ∈ $G` in a rule: the one on the left of the relation is bound, as
            # in the unbracketed `∀ $a ∈ $G ...` (see `bindop_nud`)
            match expr:
                case [Token(label='SYMBOL', value=rel), Token(label='SYMBOL', value=v), _] if is_relation(rel, kb) and v in new_consts:
                    new_consts = [v]
        if len(new_consts) != 1:
            raise KurtException(f'EvalError: expected exactly one new symbol or existing, got {new_consts} in `{expr_str(expr, kb)}`')
        new_const = new_consts[0]
        condition = expr
    return new_const, condition

# in the block that is opened, `x` will be constant
# `x` can not be an existing constant
def eval_let(kb: KnowledgeBase, expr: Expr, input_line: str, filename: str, line: int, mainstream: bool) -> KnowledgeBase:
    new_const, condition = unpack_condition(expr, kb)
    if kb.is_fixed_var(new_const):
        # `assume P $x` / `let $x` would turn the fixed `$x` of the assumption into "for all x"
        raise KurtException(f'EvalError: `{new_const}` is fixed by the assumption of an enclosing block -- `let` needs a new name')
    kb.add_const(new_const)          # add the new constant to the knowledgebase
    kb.let_names.append(new_const)
    if condition is not None:
        # the other free variables of the condition are fixed in the block, as for `assume`: in
        # `let x < $y`, `$y` is one arbitrary object, not "for all y"
        fixed = free_bound_vars(condition, kb)[0] - {new_const}
        kb.fixed_vars |= fixed
        kb.all_fixed_vars = kb.all_fixed_vars | fixed
        f = eval_use(kb, expr, input_line, 'let', filename, line, keyword='use', mainstream=False)  # use the expression as an assumption
        kb.theory_append(f)
    return kb

def eval_pick(kb: KnowledgeBase, new_const_expr: Expr, fact_expr: Expr, input_line, filename: str, line: int, mainstream: bool) -> tuple[KnowledgeBase, Expr]:
    assert isinstance(new_const_expr, Token) and new_const_expr.label=='SYMBOL'
    new_const = new_const_expr.value
    assert isinstance(new_const, str)

    # (1) parse `fact_expr`
    if not isinstance(fact_expr, list):
        fact_expr = [fact_expr]
    tokenlist: Expr = fact_expr + [end_token]                          # add end token for parse_expression
    ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))  # turn list into peekable generator
    fact = parse_expression(ts, kb, begin_rbp)     # parse the tokenlist
    fact, label, local = post_process(kb, fact)      # turn spaces into calls, symmetry, flat space operators

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
                    if equal_expr(body, fact, kb):
                        break  # end the loop without the `else` block
    else:
        raise KurtException(f'ProofError: can not find an existential formula that matches the `pick`')
    source = candidate

    # (3) open a new block, add a new constant and the fact
    kb = kb.push_level('pick', [new_const_expr])     # open a new block
    kb.add_const(new_const)                            # add the new constant to the knowledgebase
    reason = f'added as a fact for witness `{new_const}`'
    # split the input_line into LHS + 'with' + RHS
    input_line = input_line.split('with')[1].strip() if 'with' in input_line else ''
    f = Formula(kb, fact, input_line, str(line), filename, label, reason, keyword='', local=local)
    kb.theory_append(f)
    kb.pick_source, kb.pick_fact = source, f
    return kb, fact

def eval_global_format(keyword: str, args: list[Expr], kb: KnowledgeBase) -> None:
    if len(args) == 0:
        log(kb, f'format {kb.format}', '', kb.level)
    elif len(args) == 1:
        match args[0]:
            case [Token(label='SYMBOL', value=option)] if option in format_options:
                kb.format = option
                while kb.parent is not None:    # change format globally
                    kb = kb.parent
                    kb.format = option
            case _:
                options = '\n    format '.join(format_options)   # (no backslash inside an f-string's braces before Python 3.12)
                raise KurtException(f'ParseError: wrong argument, possible is:\n    format {options}')
    else:
        raise KurtException(f'ParseError: wrong arguments, possible is:\n    format {" | ".join(format_options)}')

def eval_global_toggle(keyword: str, args: list[Expr], kb: KnowledgeBase) -> None:
    value: bool = getattr(kb, keyword)   # the current value
    if len(args) == 0:
        log(kb, f'{keyword} {"on" if value else "off"}', '', kb.level)
    elif len(args) == 1:
        match args[0]:
            case [Token(label='SYMBOL', value=v)] if v in ['on', 'off']:
                node: Optional[KnowledgeBase] = kb
                while node is not None:
                    setattr(node, keyword, v == 'on')
                    node = node.parent
            case _:
                raise KurtException(f'ParseError: wrong argument, possible is:\n    {keyword} on\n    {keyword} off')
    else:
        raise KurtException(f'ParseError: wrong arguments, possible is:\n    {keyword} on\n    {keyword} off')

def generate_chain_transitivity(kb: KnowledgeBase, chain: list[str]) -> KnowledgeBase:
    # for a declared `chain [op_0, ..., op_{n-1}]` (weakest to strongest, e.g. `chain = <= <`),
    # generate and register the genuine two-fact transitivity inference for every ordered
    # pair: `$a op_i $b and $b op_j $c implies $a op_max(i,j) $c` -- reusing exactly the "pick
    # the operator with the larger index" rule `get_chain_op` already uses to combine
    # operators within one manually-*written* chain expression (`a = b <= c` concludes
    # `a <= c`), now applied as a real inference rule spanning two separately-proven facts,
    # rather than leaving every theory to hand-write its own (as arith.kurt used to for its
    # `<`/`<=`/`=` chain -- see doc/kurt-soundness.md for the writeup and arith.kurt's own
    # trimmed-down transitivity section for the before/after).
    # a chain's operators relate either two boolean arguments (e.g. `iff`/`implies`, where
    # `bool iff 0 1 2` marks positions 1 and 2 boolean too, not just the result) or two
    # ordinary/non-boolean ones (e.g. `<`/`<=`/`=`, where only the result, position 0, is
    # boolean) -- pick `%`- or `$`-prefixed schema variables to match, since a `%`-prefixed
    # name is unconditionally boolean-typed and a bare argument like `$a` defaults to
    # non-boolean (see `is_bool`/`bool_expr`), and using the wrong one fails type-checking.
    arg_is_bool = any(1 in kb.bool_sig(op) for op in chain)
    va, vb, vc = ('%A', '%B', '%C') if arg_is_bool else ('$a', '$b', '$c')
    lines = []
    n = len(chain)
    for i in range(n):
        for j in range(n):
            op_i, op_j, op_k = chain[i], chain[j], chain[max(i, j)]
            lines.append(f'use ({va} {op_i} {vb}) and ({vb} {op_j} {vc}) implies ({va} {op_k} {vc}) "chain-trans-{i}-{j}"')
    source = '\n'.join(lines) + '\n'
    stream = io.StringIO(source)
    stream.name = f'<chain transitivity for {chain}>'   # read_eval_loop needs a real `.name`
    return read_eval_loop(stream, kb, mainstream=False)

def inside_sandbox_or_expect(kb: KnowledgeBase) -> bool:
    # inside a (user-opened) `sandbox` or `expect` of the current file, whose content is discarded
    node: Optional[KnowledgeBase] = kb
    while node is not None and not node.is_load_boundary:
        if node.mode_str in ('sandbox', 'expect'):
            return True
        node = node.parent
    return False

def block_forbidding_use(kb: KnowledgeBase) -> Optional[str]:
    # `use` inside a proof-like block would leak an unproven axiom into a seemingly proven result
    # (e.g. `assume A` + `use B` gives `A implies B`) -- the kind of the innermost such block, or
    # `None` if `use` is fine here: at the top level of a file, or anywhere inside a `sandbox` or
    # `expect`, whose content is discarded
    innermost: Optional[str] = None
    node: Optional[KnowledgeBase] = kb
    while node is not None:
        if node.is_load_boundary or node.mode_str == 'root':
            return innermost
        if node.mode_str in ('sandbox', 'expect'):
            return None
        if innermost is None:
            innermost = node.mode_str
        node = node.parent
    return innermost

# the input lines of each file or shell session that were accepted, for `save` (see `read_eval_loop`)
accepted_lines: dict[str, list[str]] = {}

# statements that only show something: not saved
SHOWING_KEYWORDS = {'save', 'cert', 'help', 'hint', 'theory', 'syntax', 'level', 'mode', 'context', 'trail',
                    'tokenize', 'parse', 'inspect', 'verbose', 'format'}
# ... and those that only list something when they come without arguments
LISTING_KEYWORDS = {'load', 'use', 'def', 'show', 'prefix', 'infix', 'postfix', 'brackets', 'arity', 'bindop',
                    'flat', 'sym', 'bool', 'chain', 'var', 'const', 'alias'}

def is_showing_statement(first_line: str) -> bool:
    words = first_line.split(';')[0].split()
    if not words:
        return False
    return words[0] in SHOWING_KEYWORDS or (words[0] in LISTING_KEYWORDS and len(words) == 1)

def accept_statement(name: str, lines: list[str]) -> None:
    # the lines of a statement that was accepted -- unless it only shows something
    if lines and not is_showing_statement(lines[0]):
        accepted_lines.setdefault(name, []).extend(lines)

def save_str(filename: str) -> str:
    # `save`: the input lines accepted so far -- the source itself, which proves its results again
    # when it is checked (and gets its certificates in a `.kurtc`)
    lines = accepted_lines.get(filename, [])
    header = [f'; saved by `save` from {"the shell" if filename == "<stdin>" else os.path.basename(filename)}, '
              f'{time.strftime("%Y-%m-%d %H:%M")}: the lines that were accepted', '']
    return '\n'.join(header + lines) + '\n'

def eval_keyword_expression(keyword_token: Token, args: Expr, input_line, label: str, kb: KnowledgeBase, line: int, filename: str, mainstream: bool, local: bool = False) -> KnowledgeBase:
    keyword = keyword_token.value
    assert isinstance(keyword, str)
    assert isinstance(args, list)

    if keyword in ('infix', 'prefix', 'postfix', 'bool', 'arity', 'bindop', 'brackets', 'alias'):
        # a declaration changes how a symbol is read: not for the symbols of a theory of Kurt
        # (`infix Nat 50 50`, `bool Nat`, found in the soundness review of 2026-09-29)
        declared = [t.value for a in args for t in (a if isinstance(a, list) else [a])[:2 if keyword == 'brackets' else 1]
                    if isinstance(t, Token) and isinstance(t.value, str)]
        check_not_frozen(declared, keyword, filename, kb)

    # GENERAL STUFF
    if keyword == 'help':
        for k in keywords.keys(): log(kb, f'  {k:<12} {keywords[k]}')
    elif keyword == 'hint':
        eval_global_toggle(keyword, args, kb)
    elif keyword == 'verbose':
        eval_global_toggle(keyword, args, kb)
    elif keyword == 'calc':
        match args:
            case [] | [[Token(label='SYMBOL', value='on' | 'off')]]:
                eval_global_toggle(keyword, args, kb)
            case _:
                # `calc + add, - subtract, ...`: bind symbols to the calculator -- like axioms (`1 + 1 = 2`,
                # ...), so not with `--strict` outside the trusted theories, and not for the
                # symbols of a trusted theory
                check_strict(keyword, filename)
                bindings: list[tuple[str, str]] = []
                for arg in args:
                    match arg:
                        case [Token(label='SYMBOL', value=symbol), Token(label='SYMBOL', value=operation)] if isinstance(symbol, str) and isinstance(operation, str):
                            if operation not in CALCULATOR_OPERATIONS and operation not in CALCULATOR_RELATIONS:
                                raise KurtException(f'EvalError: `{operation}` is not an operation of the calculator, one of {", ".join(CALCULATOR_OPERATIONS + tuple(CALCULATOR_RELATIONS))}', keyword_token.column)
                            bindings.append((symbol, operation))
                        case _:
                            msg = create_usage(keyword, [[], ['on'], ['off'], ['SYMBOL', 'OPERATION']])
                            raise KurtException(f'ParseError: wrong arguments, possible is:\n{msg}', keyword_token.column)
                check_not_frozen([symbol for symbol, _ in bindings], keyword, filename, kb)
                for symbol, operation in bindings:
                    kb.bind_calc(symbol, operation)
                    if mainstream:
                        log(kb, f'calc {symbol} {operation}', f'computed by the calculator', kb.level)
    elif keyword == 'load':
        if len(args) == 0:
            log(kb, kb.loaded_files_str().strip())
        else:
            proof_block = block_forbidding_use(kb)
            if proof_block is not None:
                # like `use`: the loaded axioms would look proven inside the block
                raise KurtException(f'EvalError: `load` is not allowed inside `{proof_block}` -- load before the proof', keyword_token.column)
            for arg in args:
                assert isinstance(arg, list) and len(arg) == 1, f'BUG: `load` expects [[fname1], [fname2]]'
                match arg[0]:
                    case Token(label='STRING', value=fname):
                        assert isinstance(fname, str)
                        s_paths = [Path(filename).parent.resolve()] + theory_path
                        already_loaded = is_already_loaded(fname, kb, s_paths)
                        try:
                            kb = load_file(fname, kb, search_paths=s_paths, mainstream=False)
                        except KurtException as e:
                            if e.column is None:
                                e.column = arg[0].column
                            raise
                        if mainstream:
                            reason = decorate_reason(mainstream, 'already loaded, skipped' if already_loaded else 'loaded', filename, str(line))
                            log(kb, f'load {fname}', reason, kb.level)
                    case _:
                        assert False, f'BUG: `load` was scanned with wrong args'

    elif keyword == 'save':
        if len(args) != 1:
            raise KurtException(f'ParseError: `save` expects exactly one filename, e.g. `save "state.kurt"`', keyword_token.column)
        arg = args[0]
        assert isinstance(arg, list) and len(arg) == 1, f'BUG: `save` expects [[fname]]'
        match arg[0]:
            case Token(label='STRING', value=fname):
                assert isinstance(fname, str)
                # `save` writes a Kurt file of the checked one or the shell, nothing else (found in
                # the soundness review of 2026-09-29: it could overwrite any file, also when grading)
                if strict_mode:
                    raise KurtException(f'EvalError: no `save` with `--strict`', keyword_token.column)
                if len(_loading_in_progress) > 1:
                    raise KurtException(f'EvalError: `save` only in the file that is checked (or the shell), not in a loaded one', keyword_token.column)
                if not fname.endswith('.kurt'):
                    raise KurtException(f'EvalError: `save` writes a Kurt file, its name must end with `.kurt`, e.g. `save "state.kurt"`', arg[0].column)
                if packaged_theory_file(os.path.basename(fname)) is not None:
                    raise KurtException(f'EvalError: `{os.path.basename(fname)}` is the name of a theory that comes with Kurt -- `save` under another name', arg[0].column)
                if open_block_depth(kb) > 0:
                    raise KurtException(f'EvalError: `save` only outside of blocks -- close the open blocks first', keyword_token.column)
                if any(len(node.show) > 0 for node in [kb] + ([kb.parent] if kb.parent is not None else [])):
                    raise KurtException(f'EvalError: `save` only without pending `show` goals -- prove them first', keyword_token.column)
                content = save_str(filename)
                try:
                    with open(fname, 'w') as fh:
                        fh.write(content)
                except OSError as e:
                    raise KurtException(f'EvalError: `save` could not write `{fname}`: {e}', arg[0].column)
                if mainstream:
                    log(kb, f'save "{fname}"', f'wrote {fname}', kb.level)
            case _:
                assert False, f'BUG: `save` was scanned with wrong args'

    elif keyword == 'parse':
        if len(args) > 0:
            msg = '; sexpr\n'
            for args_i in args:
                msg += f'{expr_sexpr(args_i, kb)}, '
            msg = msg[:-2] + '\n' # remove last ', ' and add newline
            msg += '; syntax info'
            info = ''
            for args_i in args:
                tokens = get_token_set(args_i)
                for t in tokens:
                    info += '\n' + kb.info(t)
            info = '\n'.join(sorted([line for line in info.split('\n') if len(line) > 0]))
            msg += f'\n{info}'
            if mainstream:
                log(kb, msg)
    elif keyword == 'tokenize':
        if len(args) > 0:
            parts = []
            for args_i in args:
                tokenlist: Expr = args_i + [end_token]                             # add end token for parse_expression
                ts: PeekableGenerator = PeekableGenerator((t for t in tokenlist))  # turn list into peekable generator
                parts.append("  ".join([str(t) for t in ts]))
            msg = '\n'.join(parts)
            if mainstream:
                log(kb, msg)
    elif keyword == 'format':
        eval_global_format(keyword, args, kb)
    elif keyword == 'level':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        if mainstream:
            log(kb, str(kb.level))
    elif keyword == 'mode':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        if mainstream:
            log(kb, kb.mode_str)
    elif keyword == 'trail':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        msg = f'{kb.mode_str}'
        kb_parent = kb.parent
        while kb_parent is not None:
            msg = f'{kb_parent.mode_str} > ' + msg
            kb_parent = kb_parent.parent
        msg = '; ' + msg
        if mainstream:
            log(kb, msg)
    elif keyword == 'context':
        if len(args) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments', keyword_token.column)
        
        msg = kb.nice_mode_str()
        kb_parent = kb.parent
        while kb_parent is not None:
            msg = kb_parent.nice_mode_str() + '\n' + msg
            kb_parent = kb_parent.parent
        if mainstream:
            log(kb, msg)


    # SYNTAX RELATED
    elif keyword == 'syntax':
        if len(args) == 0:
            msg = kb.syntax_str_all_levels().strip()
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
        if mainstream:
            log(kb, msg)
    elif keyword == 'prefix':
        if len(args) == 0:
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            check_chain_not_frozen(chain, filename, kb)
            check_strict(keyword, filename)   # a chain generates transitivity axioms
            new_stuff.append(chain)    # first collect
        for chain in new_stuff:
            kb.add_chain(chain)
            kb = generate_chain_transitivity(kb, chain)

    elif keyword == 'flat':
        if len(args) == 0:
            log(kb, kb.dict_or_set_str_all_levels(keyword))
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        if new_stuff:
            check_strict(keyword, filename)     # a claim about the operator, like an axiom
        check_not_frozen(new_stuff, keyword, filename, kb)
        for op in new_stuff:
            kb.add_flat(op)
    elif keyword == 'sym':
        if len(args) == 0:
            log(kb, kb.dict_or_set_str_all_levels(keyword))
        new_stuff = []
        for arg in args:
            match arg:
                case [Token(label='STRING'|'SYMBOL', value=op)]:
                    assert isinstance(op, str)
                    new_stuff.append(op)    # first collect
                case _:
                    msg = create_usage(keyword, [[], ['STRING']])
                    raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
        if new_stuff:
            check_strict(keyword, filename)     # a claim about the operator, like an axiom
        check_not_frozen(new_stuff, keyword, filename, kb)
        for op in new_stuff:
            kb.add_sym(op)
    elif keyword == 'bool':
        if len(args) == 0:
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
                log(kb, f'var {op}', f'added variable', kb.level)
    elif keyword == 'const':
        if len(args) == 0:
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
            if op[0] in ['$', '%']:
                # (inside a `let`, such a symbol does become a fixed, arbitrary constant)
                raise KurtException(f'EvalError: symbol `{op}` starts with `{op[0]}`, so it is always a variable and can not be declared a constant', keyword_token.column)
            kb.add_const(op)
            if mainstream:
                log(kb, f'const {op}', f'added constant', kb.level)
    elif keyword == 'alias':
        if len(args) == 0:
            log(kb, kb.dict_or_set_str_all_levels(keyword))
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
    elif keyword == 'cert':
        wanted: list[int] = []
        for arg in args:
            match arg:
                case [Token(label='INT', value=n)] if isinstance(n, int):
                    wanted.append(n)
                case _:
                    raise KurtException(f'ParseError: `cert` takes line numbers, e.g. `cert 17`', keyword_token.column)
        if not wanted:
            earlier = [n for (f, n) in certificates_by_line if f == filename and n < line]
            wanted = [max(earlier)] if earlier else []
        msgs = []
        for n in wanted:
            certs = certificates_by_line.get((filename, n), [])
            if not certs:
                msgs.append(f'; line {n}: no certificate (no step, or not a line of this file)')
            for i, (cert, problem) in enumerate(certs):
                part = f' ({i+1} of {len(certs)})' if len(certs) > 1 else ''
                msgs.append(f'; line {n}{part}:\n' + certificate_str(cert, problem, kb, filename))
        if mainstream:
            log(kb, '\n'.join(msgs) if msgs else '; no certificate yet')

    elif keyword == 'theory':
        if len(args) == 0:
            log(kb, kb.theory_str().strip())
        else:
            msg = ''
            for arg in args:
                match arg:
                    case [Token(label='STRING'|'SYMBOL', value=s)]:
                        assert isinstance(s, str)
                        info = kb.theory_str(op=s).strip()
                        if len(info) > 0:
                            msg += info + '\n'
                    case _:
                        msg = create_usage(keyword, [[], ['STRING'], ['SYMBOL']])
                        raise KurtException(f'ParseError: wrong number of arguments, possible is:\n{msg}', keyword_token.column)
            msg = '\n'.join(sorted([line for line in msg.split('\n') if len(line) > 0]))
            log(kb, msg)

    elif keyword == 'use':
        if len(args) == 0:
            log(kb, kb.theory_str(keyword=keyword).strip())
        else:
            proof_block = block_forbidding_use(kb)
            if strict_mode and proof_block is None and not inside_sandbox_or_expect(kb):
                check_strict(keyword, filename)
            if proof_block is not None:
                raise KurtException(f'EvalError: `use` is not allowed inside `{proof_block}` -- the result would look proven although it relies on this axiom; state it before the proof, or use `todo`', keyword_token.column)
            formulas = []
            for expr in args:
                try:
                    formulas.append(eval_use(kb, expr, input_line, label, filename, line, mainstream, keyword, local))  # use the expression as an assumption
                except KurtException:
                    # let's forget about the new `formulas` and raise an exception
                    raise
            for f in formulas:
                kb.theory_append(f)
                if mainstream:
                    log(kb, f.formula_str(kb), f.reason, kb.level)

    elif keyword == 'def':
        if len(args) == 0:
            log(kb, kb.theory_str(keyword=keyword).strip())
        else:
            proof_block = block_forbidding_use(kb)
            if proof_block is not None:
                # like `use`: a symbol defined inside a block would leave it with a meaning that
                # depends on the block's constants (`let x` / `def k iff P x` gives `∀ x (k iff P x)`)
                raise KurtException(f'EvalError: `def` is not allowed inside `{proof_block}` -- define it before the proof (or use `let` with a condition)', keyword_token.column)
            formulas = []
            lhs_consts = []
            for expr in args:
                try:
                    f, lc = eval_def(kb, expr, input_line, label, filename, line, mainstream, local)  # use the expression as a definition
                    formulas.append(f)
                    lhs_consts.append(lc)
                except KurtException:
                    # let's forget about the `formulas` and `lhs_consts`
                    raise
            for (f, lc) in zip(formulas, lhs_consts):
                kb.theory_append(f)
                if lc in new_symbols:
                    new_symbols.remove(lc)    # `def` is how it gets declared
                if mainstream:
                    reason = f'{line} defining `{lc}`'
                    log(kb, f'def {expr_str(f.expr, kb)}', reason, kb.level-1)  # log the new constant

    elif keyword == 'todo':
        check_strict(keyword, filename)
        # works like a joker!  however, what to store in the theory?  add a todo token
        if len(args) == 0:
            # `todo` inside proofs, a joker for the next statement, even a `qed`
            kb.theory_append(eval_use(kb, todo_token, input_line, label, filename, line, mainstream, keyword))  # use the expression as an assumption
            todo = decorate_reason(False, f'todo', filename, str(line))
            kb.todo_add(todo)
            if mainstream:
                log(kb, 'todo', decorate_reason(mainstream, 'admits the next step, still to do', filename, str(line)), kb.level)
        else:
            for expr in args:
                # `todo F`, adds `F` like an axiom and takes a note of the todo
                f = eval_use(kb, expr, input_line, label, filename, line, mainstream, keyword)
                kb.theory_append(f)  # use the expression as an assumption
                todo = decorate_reason(False, f'todo {expr_str(expr, kb)}', filename, str(line))
                kb.todo_add(todo)
                if mainstream:
                    log(kb, f'todo {expr_str(expr, kb)}', decorate_reason(mainstream, 'admitted, still to do', filename, str(line)), kb.level)

    elif keyword == 'qed':            # closes the last block (scope) and checks that the last promised formula has been proved
        assert False, '`qed` should have been handled in `scan_parse_check_eval`'
        pass    # do nothing, it was already handled in `scan_parse_check_eval`

    elif keyword == 'break':
        assert False, '`break` should have been handled in `scan_parse_check_eval`'
        pass    # do nothing, it was already handled in `scan_parse_check_eval`

    elif keyword == 'inspect':
        raise NotImplementedError('`inspect` keyword is not yet implemented')
        # implementation idea:
        # raise some special exception that is caught in the main loop
        # that exception would open an interactive shell with access to the current knowledgebase

    elif keyword == 'show':
        if len(args) == 0:
            log(kb, kb.show_str().strip())
        elif len(args) == 1:
            expr = args[0] if len(args) == 1 else args  # allow single expression or a list of expressions
            kb = eval_show(kb, expr, input_line, label, filename, line, mainstream, local)
        else:
            raise KurtException(f'ParseError: `show` takes only one formula, no comma-separated list allowed')

    elif keyword == 'proof':                  # opens a new block (scope)
        if len(args) > 0:
            raise KurtException(f'EvalError: `{keyword}` takes no arguments')
        kb = eval_proof(kb, mainstream)

    elif keyword == 'sandbox':
        if len(args) > 0:
            raise KurtException(f'EvalError: `{keyword}` takes no arguments')
        kb = kb.push_level('sandbox', [])
        log(kb, f'sandbox', f'{line} open sandbox, close with `break`', kb.level-1)  # log the new constant

    elif keyword == 'expect':
        msg = 'EvalError: `expect` takes exactly one string argument naming the expected error kind, e.g. `expect "ProofError"`'
        if len(args) != 1:
            raise KurtException(msg)
        match args[0]:
            case [Token(label='STRING', value=expected_kind)] if expected_kind in KurtException.KNOWN_KINDS:
                assert isinstance(expected_kind, str)
            case [Token(label='STRING', value=bad_kind)]:
                raise KurtException(f'EvalError: unknown error kind `{bad_kind}` for `expect`, expected one of {KurtException.KNOWN_KINDS}')
            case _:
                raise KurtException(msg)
        kb = kb.push_level('expect', [Token(label='STRING', value=expected_kind)])
        if mainstream:
            log(kb, f'expect "{expected_kind}"', f'{line} open block, expect a `{expected_kind}` inside', kb.level-1)

    elif keyword == 'assume'  or  keyword == 'case':
        if len(args) != 1:
            raise KurtException(f'EvalError: `{keyword}` takes a single expression as argument')
        expr = args[0]
        fixed = free_bound_vars(expr, kb)[0]   # fixed in the block, see `is_var`
        kb = kb.push_level('assume', args)  # open a new block
        kb.fixed_vars = set(fixed)
        kb.all_fixed_vars = kb.all_fixed_vars | fixed
        try:
            f = eval_use(kb, expr, input_line, label, filename, line, mainstream=False, keyword='use')  # use the expression as an assumption
            kb.theory_append(f, symbol_level_prev=True)
        except KurtException:
            kb = kb.pop_level()
            raise
        if mainstream:
            reason = f'{line} open block with assumption'
            assumptions_str = ', '.join([expr_str(arg, kb) for arg in args])
            log(kb, f'{keyword} {assumptions_str}', reason, kb.level-1)  # log the new constant

    elif keyword == 'let':
        msg = 'EvalError: `let` takes new constants or boolean expressions'
        if len(args) == 0:
            raise KurtException(msg)
        # add the new constants and their constraints (if boolean expressions are given)
        kb = kb.push_level('let', args)  # open a new block
        for expr in args:  # args is a list of expressions
            try:
                kb = eval_let(kb, expr, input_line, filename, line, mainstream)
            except KurtException:
                kb = kb.pop_level()  # close the block on error
                raise      # the same exception again
        if mainstream:
            reason = f'{line} open local scope with (possibly constrained) new constants'
            args_str = [expr_str(expr, kb) for expr in args]
            log(kb, f'{keyword} {", ".join(args_str)}', reason, kb.level-1)  # log the new constants

    elif keyword == 'pick':
        msg = 'EvalError: `pick` takes a new constant, keyword `with` and a formula , e.g. `pick x with F(x)`'
        if len(args) == 0:
            raise KurtException(msg)
        if len(args) > 1:
            # each `pick` opens a block of its own, but the next line can only indent once
            raise KurtException('EvalError: one `pick` per line -- write the next `pick` inside the block of the first')
        for expr in args:
            # unlike `let`/`assume`/`case`, `eval_pick` pushes its own level *internally*,
            # only after checking that a matching existential exists -- so it can raise
            # (e.g. "can not find an existential formula that matches the `pick`") before
            # any level was actually opened. Only pop here if `eval_pick` got that far;
            # otherwise this would wrongly discard the caller's own already-open level
            # (found via a crash inside `expect "ProofError" / pick ...`, see
            # doc/kurt-soundness.md #3.4).
            level_before = kb.level
            try:
                # `pick`'s args never went through `parse_expression` (it's not in
                # `keywords_with_parsing`, see `parse_tokenstream`) -- `expr` here is still a
                # flat list of raw tokens, split only on top-level commas, not a parsed
                # expression tree; `with` is where the new constant ends and the fact begins.
                match expr:
                    case [*tail] if sum(1 for t in tail if is_helper_keyword(t)) == 1:
                        with_index = next(i for i, t in enumerate(tail) if is_helper_keyword(t))
                        pre_with, fact_expr = tail[:with_index], tail[with_index+1:]
                        if not fact_expr:
                            raise KurtException(msg)                  # `pick x with` without a fact
                        if len(pre_with) != 1:
                            raise KurtException(f'EvalError: `pick` does not support an extra condition on the new constant (only `pick x with FACT`), got `{" ".join(str(t.value) for t in pre_with)}`' if len(pre_with) > 1 else msg)
                        new_const_expr = pre_with[0]
                        # reuse `let`'s own "extract the one new-or-existing symbol" parsing
                        # (`unpack_condition`) for consistency -- but unlike `let x>0`, which
                        # quantifies its condition away as an assumption when the block closes
                        # (§9.2), a `pick`ed witness is existential, so it can never carry an
                        # inline condition of its own: an extra condition here would be an
                        # unproven fact asserted about a specific value with no justification --
                        # a soundness hole, not a convenience. The witness's only property comes
                        # from matching the existential's own body (below). In practice this
                        # branch of `unpack_condition` is unreachable today: `pre_with` is
                        # always exactly one raw token (nothing upstream parses it into a
                        # compound expression), so `condition` is always `None` here already --
                        # the check stays as a clear, deliberate guard, not dead code, in case
                        # that ever changes.
                        new_const, condition = unpack_condition(new_const_expr, kb)
                        if condition is not None:
                            raise KurtException(f'EvalError: `pick` does not support an extra condition on the new constant (only `pick x with FACT`), got `{expr_str(new_const_expr, kb)}`', get_column(new_const_expr))
                        if kb.is_const(new_const):
                            raise KurtException(f'EvalError: `pick` requires a new constant or existing variable, got already-declared constant `{new_const}`')
                        if kb.is_fixed_var(new_const):
                            raise KurtException(f'EvalError: `{new_const}` is fixed by the assumption of an enclosing block -- `pick` needs a new name')
                        kb, fact = eval_pick(kb, new_const_expr, fact_expr, input_line, filename, line, mainstream)
                    case _:
                        raise KurtException(msg)
            except KurtException:
                if kb.level > level_before:
                    kb = kb.pop_level()
                raise
        if mainstream:
            reason = f'{line} open local scope with new constant `{new_const}`'
            log(kb, f'{keyword} {new_const} with {expr_str(fact, kb)}', reason, kb.level-1)  # log the new constants
    elif keyword == LOCAL_SYMBOL:
        raise KurtException(f'SyntaxError: `{LOCAL_SYMBOL}` marks a label and comes after the formula, e.g. `use A implies A {LOCAL_SYMBOL} "a"`')
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
    # the formulas of `use A, B, C`: the comma is right-associative, so this is `A, (B, C)`
    match e:
        case [Token(label='SYMBOL', value=v), head, rest] if v == COMMA_SYMBOL:
            return [head] + chop_off_comma(rest)
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

def eval_expression(keyword_token: Optional[Token], expr_list: list[Expr], input_line: str, label: str, kb: KnowledgeBase, line: int, filename: str, mainstream: bool, local: bool = False) -> KnowledgeBase:
    if keyword_token is None:
        # expression without keyword: try to derive the formula and add it to the theory
        if len(expr_list) == 0:
            return kb
        for expr in expr_list:
            if not bool_expr(expr, kb, strict=False):   # not strict, since we are possibly adding new symbols
                raise KurtException(f'EvalError: must evaluate to boolean, got `{expr_str(expr, kb)}`')
            if len(kb.theory) > 0:
                last_formula = kb.theory[-1]
                if equal_expr(last_formula.expr, expr, kb):
                    # short-cut to avoid duplicates: restating the last formula is logged, not added again
                    if mainstream:
                        reason = decorate_reason(mainstream, f'by {formula_ref(last_formula, filename, mainstream)}', filename, str(line))
                        restated = Formula(kb, expr, input_line, str(line), filename, label, reason, keyword='')
                        log(kb, restated.formula_str(kb), reason, kb.level)
                    continue
            unknown = undeclared_symbols(expr, kb)
            if len(unknown) > 0 and strict_mode and not is_trusted_file(filename):
                raise KurtException(f'EvalError: {", ".join(f"`{n}`" for n in unknown)} not declared -- with `--strict`, every symbol must be declared before its use (`const`, `var`, `bool`, ...)')
            try:
                certs, _ = derive_expr(expr, filename, mainstream, State.empty(), kb)  # this might raise ProofError exceptions
                reasons = [c.short(filename, mainstream) for c in certs]
            except KurtException as e:
                if len(unknown) > 0:
                    e.msg += f' -- note: {", ".join(f"`{n}`" for n in unknown)} {"was" if len(unknown) == 1 else "were"} never declared or used before, a typo?'
                raise
            if len(reasons) == 1:
                reason = reasons[0]
            else:
                assert len(reasons) > 1
                assert isinstance(expr, list) and len(expr) > 2
                assert len(expr) == len(reasons) + 1
                line_strs: list[str] = []
                for clause, reason, letter in zip(expr[1:], reasons, letter_generator()):
                    line_str = str(line) + letter
                    line_strs.append(line_str)
                    reason = decorate_reason(mainstream, reason, filename, line_str)
                    # each conjunct is its own, unlabelled intermediate step -- `label` (the
                    # claim's own label, if any) belongs on the *combined* formula below, not
                    # here; a same-named local would clobber the outer `label` this loop runs
                    # before reaching, silently discarding the combined formula's label
                    sub_f = Formula(kb, clause, input_line, line_str, filename, '', reason, keyword='')
                    kb.theory_append(sub_f)                         # add sub to the knowledge base
                    if mainstream:
                        log(kb, sub_f.formula_str(kb), reason, kb.level)
                reason = f'by and-intro({", ".join(line_strs)})'
            # a bare claim can be labelled too, exactly like `use`/`show` -- same mechanism,
            # since every statement (bare or keyworded) shares `check_expr_label`/`post_process`
            if len(label) > 0:
                reason += f' "{label}"'
            reason = decorate_reason(mainstream, reason, filename, str(line))
            f = Formula(kb, expr, input_line, str(line), filename, label, reason, keyword='', local=local)
            kb.theory_append(f)                         # add it to the knowledge base
            if mainstream:
                log(kb, f.formula_str(kb), reason, kb.level)
        return kb
    else:
        # expression with a keyword
        return eval_keyword_expression(keyword_token, expr_list, input_line, label, kb, line, filename, mainstream, local)

########################
## kurt type checking ##
########################

def bool_expr(expr: Expr, kb: KnowledgeBase, strict: bool=True) -> bool:
    # this is the non-deep check
    # - at some places we are strict
    # - at other places (like eval_use) we are not strict, since we are adding a new formula
    match expr:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and (kb.is_var(v) or kb.is_fixed_var(v)) and kb.is_bool(v):
            return True                    # boolean variables (also when fixed by an assumption)
        case Token(label='SYMBOL', value=v):
            assert isinstance(v, str)
            if strict or kb.is_used(v):
                return 0 in kb.bool_sig(v)
            else:
                if v[0] == '$':
                    return False
                elif v[0] == '%':
                    return True
                else:
                    return True   # not used yet and unclear name!  so it will soon be boolean
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
            if expr.column is None:
                return 0
            else:
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
            assert isinstance(v, str), f'BUG: a token with label `SYMBOL` must have string-valued value'
            if not is_var_token(var_x, kb):
                raise KurtException(f'TypeError: first arg of `sub` must be variable symbol, got `{expr_str(var_x, kb)}`', column=expr_column(var_x))
            assert isinstance(var_x, Token) and isinstance(var_x.value, str)
            bv = kb.is_bool(var_x.value)         # a bool variable
            be = bool_expr(a, kb)
            if bv and not be:
                raise KurtException(f'TypeError: first arg of `sub` is boolean variable, but second is not', column=expr_column(a))
            if be and not bv:
                raise KurtException(f'TypeError: first arg of `sub` is variable, but second is boolean expression', column=expr_column(a))
            type_check_expression(A, kb)

        # most expressions: prefix, postfix, infix, bindop (but not `sub`, see above), ...
        case [Token(label='SYMBOL', value=op), *tail]:
            assert isinstance(op, str)
            # (1) do the args fit the declared type in `bool_sig`
            for idx in range(1, len(expr)):
                ei = expr[idx]
                if idx in kb.bool_sig(op) and not bool_expr(ei, kb, strict=False):
                    if ei != LHS_token:
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
                    case _:     # e.g. a number, `∀ 1 (P 1)`
                        raise KurtException(f'TypeError: first arg of binding operator must be a variable or a condition, got `{expr_str(tail[0], kb)}`', column=expr_column(tail[0]))
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

# the comment the user wrote on the line being evaluated: shown by the first output line with a
# reason, whose reason then goes on the next line (see `log`)
current_comment: list[Optional[str]] = [None]

def comment_of(line: str) -> Optional[str]:
    # what follows the first `;` outside of a string, if anything
    in_string = False
    for i, ch in enumerate(line):
        if ch == '"':
            in_string = not in_string
        elif ch == ';' and not in_string:
            rest = line[i+1:].strip()
            return rest if rest else None
    return None

@contextlib.contextmanager
def users_comment(line: str) -> Iterator[None]:
    outer = current_comment[0]
    current_comment[0] = comment_of(line)
    try:
        yield
    finally:
        current_comment[0] = outer

def log(kb: KnowledgeBase, s: str, reason: str='', level: Optional[int]=None) -> None:
        if level is not None and level > 0 and kb.tmp:
            level = level - 1
        indent: str = '' if level is None else ' ' * (proof_indent * level)
        if len(reason) == 0:
            line = indent+s
        elif current_comment[0] is not None:
            # the user's comment stays on the line, the reason goes below it
            line = f'{(indent+s):<{comment_indent}}; {current_comment[0]}\n{"":<{comment_indent}}; {reason}'
            current_comment[0] = None
        else:
            line = f'{(indent+s):<{comment_indent}}; {reason}'
        print(line, file=sys.stdout)

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
        case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and kb.is_bindop(op):
            bound_v, _ = unpack_condition(cond, kb)
            body = expr[2:]
            new_s = s.block_always(bound_v)
            new_cond = apply_subst(cond, new_s, kb)
            new_body = [apply_subst(c, new_s, kb) for c in body]
            return [expr[0], new_cond, *new_body]
        
        # general case: recurse into all children
        case [*exprs]:
            return [apply_subst(c, s, kb) for c in exprs]
        
        # never reach this one!
        case _:
            assert False, f'BUG: did not match expression `{expr_str(expr, kb)}` in `apply_subst`'

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
        case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and kb.is_bindop(op):
            bound_v, opt_condition = unpack_condition(cond, kb)
            fv, bv = free_bound_vars(tail, kb)
            if opt_condition is not None:
                fv_cond, bv_cond = free_bound_vars(opt_condition, kb)
                fv.update(fv_cond)
                bv.update(bv_cond)
            if bound_v in fv:           # `bound_v` appears freely in `tail` or `opt_condition`
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

# the name each internal variable stands for, e.g. `$$07` for the `$x` of a rule -- to show
# certificates with the names as written (see `readable_names`)
origin_names: dict[str, str] = {}

def note_origin(new: str, origin: Optional[str]) -> str:
    if origin is not None:
        origin_names[new] = origin_names.get(origin, origin)
    return new

# new variable names just for internal use
def new_var_name(origin: Optional[str] = None) -> str:
    if not hasattr(new_var_name, "counter"):
        new_var_name.counter = 0            # static variable of the function
    new_var_name.counter += 1               # get a new number
    # use format like this: $$07
    return note_origin(f'$${new_var_name.counter:02d}', origin)   # the `$$` ensures that it is not a kurt variable that the user can define

# new boolean variable names just for internal use
def new_bool_var_name(origin: Optional[str] = None) -> str:
    if not hasattr(new_bool_var_name, "counter"):
        new_bool_var_name.counter = 0             # static variable of the function
    new_bool_var_name.counter += 1                # get a new number
    # use format like this: %%07
    return note_origin(f'%%{new_bool_var_name.counter:02d}', origin)   # the `%%` ensures that it is not a kurt variable that the user can define

def replace_token_value(expr: Expr, old_value: str, new_token: Token) -> Expr:
    # pure structural replacement of every occurrence of a specific token value -- unlike
    # `apply_subst`, this does NOT respect binder scoping (it will happily rewrite a bindop's
    # own binder slot too). Only safe to use when `old_value` is a synthetic, globally-unique
    # name that cannot collide with some other, unrelated variable of the same name in a
    # different scope -- see `strip_premise_with_synced_conclusion`, its one caller.
    if isinstance(expr, Token):
        return new_token if expr.value == old_value else expr
    return [replace_token_value(e, old_value, new_token) for e in expr]

def remove_outer_forall_quantifiers(expr: Expr, kb: KnowledgeBase) -> tuple[Expr, tuple[str, ...]]:
    # this function must remove all outer universal quantifiers
    # if there is a condition, it turns it into an implication
    # Returns (stripped_expr, fresh_vars): `fresh_vars` are the freshly-generated names that
    # stood in for the removed quantifiers' bound variables. A caller using the result as a
    # *premise to search for* (as opposed to a conclusion to unify against a real goal) MUST
    # block these from being unified away to a specific value: they represent a genuinely
    # arbitrary/generic instance ("true for all x"), and letting the search bind them to
    # whatever's convenient defeats the whole point of universal generalization -- see
    # doc/kurt-soundness.md's writeup of the `impl_elim` bug this was added to fix.
    expr = deepcopy_expr(expr)  # deep copy to avoid modifying the original expression
    fresh_vars: list[str] = []  # in the order of the quantifiers (the kernel repeats the stripping)

    # chop off all outer universal quantifiers that have **no condition** and rename their bound
    # vars -- a quantifier with a condition, `∀ $x > 0 ...`, stays: what it means is said by the
    # rules of logic.kurt ("forall-cond-elim", "forall-cond-def"), not by the engine
    while is_forall(expr):
        # `is_forall` only checks the head symbol, not that it's really a bindop-shaped
        # `[forall, bound-var, body]` triple -- if `forall` isn't declared a `bindop` at all
        # (should not happen since it's hardcoded in `initial_kb`, but this runs on every
        # stored formula, so fail cleanly rather than crash if that invariant is ever broken)
        # it can parse as a plain, flatly space-applied symbol instead, with a different shape.
        if not (isinstance(expr, list) and len(expr) == 3):
            raise KurtException(f'EvalError: `forall` is not declared as a proper binding operator, got `{expr_str(expr, kb)}`')
        if not isinstance(expr[1], Token):
            break
        assert isinstance(expr[1].value, str)
        bound_var = expr[1].value
        expr = expr[2]
        free_var = new_bool_var_name(bound_var) if kb.is_bool(bound_var) else new_var_name(bound_var)
        fresh_vars.append(free_var)
        s = State({bound_var: Token(label='SYMBOL', value=free_var)}, frozenset(), frozenset())
        expr = apply_subst(expr, s, kb)
    return expr, tuple(fresh_vars)

def strip_premise_with_synced_conclusion(premise_raw: Expr, conclusion_raw: Expr, kb: KnowledgeBase) -> tuple[Expr, Expr, tuple[str, ...]]:
    # like `remove_outer_forall_quantifiers`, but for an implication's PREMISE specifically,
    # where the SAME bound variable(s) may also occur in the CONCLUSION -- e.g. forall-elim's
    # own axiom, `(forall $x %A) implies (sub $x $a %A)`, where `$x` appears in both halves.
    # Renaming must be applied identically to both sides to keep them in sync: doing it via
    # two independent `remove_outer_forall_quantifiers` calls (the first version of this fix)
    # silently generated a fresh name for the premise's own copy of `$x` that then went
    # unused, since `%A` is an opaque schema token that doesn't literally contain `$x` to
    # rename -- meaning the conclusion's *original*, un-renamed `$x` was the one that actually
    # ended up inside whatever `%A` got matched to, and blocking the (wrong, unused) fresh
    # name from the premise-only rename didn't block anything real. See
    # doc/kurt-soundness.md's writeup of the underlying `impl_elim` soundness bug.
    premise = deepcopy_expr(premise_raw)
    conclusion = deepcopy_expr(conclusion_raw)
    fresh_vars: list[str] = []
    while is_forall(premise):
        if not (isinstance(premise, list) and len(premise) == 3):
            raise KurtException(f'EvalError: `forall` is not declared as a proper binding operator, got `{expr_str(premise, kb)}`')
        if not isinstance(premise[1], Token):
            break               # a condition stays, see `remove_outer_forall_quantifiers`
        assert isinstance(premise[1].value, str)
        bound_var = premise[1].value
        premise = premise[2]
        free_var = new_bool_var_name(bound_var) if kb.is_bool(bound_var) else new_var_name(bound_var)
        fresh_vars.append(free_var)
        fresh_token = Token(label='SYMBOL', value=free_var)
        # a pure structural (non-capture-avoiding) rename, not `apply_subst`: `apply_subst`
        # deliberately protects a bindop's own binder slot from substitution (correct for
        # ordinary substitution, since you must never substitute into a variable's own
        # binding declaration) -- but `sub` is itself a bindop, so it would refuse to rename
        # `bound_var` inside the conclusion's own `sub $x $a %A` binder position, leaving
        # premise and conclusion referring to two different names for what must be the same
        # variable. Safe here specifically because `bound_var` is always a synthetic,
        # globally-unique name (from `rename_all_vars`'s own counter): there's no risk of
        # accidentally renaming some other, unrelated variable that just happens to share it.
        premise = replace_token_value(premise, bound_var, fresh_token)
        conclusion = replace_token_value(conclusion, bound_var, fresh_token)
    return premise, conclusion, tuple(fresh_vars)
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
        case Token(label='SYMBOL', value=var) if isinstance(var, str) and not kb.is_const(var) and (kb.is_var(var) or var in bound_vars):
            new_expr = s.lookup(var)
            if new_expr is None:
                if var in bound_vars or kb.is_var(var):
                    # note that `bound_vars` do not have to be declared as variables in `kb`, since they are bound they must be variables
                    if kb.is_bool(var):
                        # a bound variable that is boolean must begin with `%`
                        new_var = new_bool_var_name(var)
                    else:
                        new_var = new_var_name(var)
                else:
                    raise KurtException(f'BUG: variable `{var}` is neither a variable nor a boolean variable, but appears in the expression `{expr_str(expr, kb)}`')
                new_expr = Token(label='SYMBOL', value=new_var, column=expr.column, origin=expr.origin)
            return new_expr, s.bind(var, new_expr)  # extend the state with the new binding

        # any other token is not modified
        case Token():
            return expr, s

        # binding operator expression
        case [Token(label='SYMBOL', value=bind_op), cond, *body] if isinstance(bind_op, str) and kb.is_bindop(bind_op):
            bind_var, opt_condition = unpack_condition(cond, kb)

            # operator gets processed with current scope (actually nothing to do)
            head1, s = rename_all_vars_rec(expr[0], kb, s, bound_vars)

            # extend the scope with the new bound variable
            new_bound_vars = bound_vars | {bind_var}

            # `cond` and `body` are processed in the context, that `bind_var in bound_vars` hold
            head2, s = rename_all_vars_rec(cond, kb, s, new_bound_vars)

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


def valid_bindop_conditions(expr: Expr, kb: KnowledgeBase) -> bool:
    # whether every binding operator in `expr` still has a proper condition (bound variable)
    try:
        free_bound_vars(expr, kb)    # raises if some condition is not of the right shape
        return True
    except KurtException:
        return False

def generate_all_combinations(expr: Expr, token_x: Token, expr_a: Optional[Expr], kb: KnowledgeBase) -> Iterator[tuple[Optional[Expr], Expr]]:
    # generate all `($a, %A)` such that `expr == sub $x $a %A`
    # (alternatively: all `($a, %A)` such that `expr == sub %x %a %A`)
    # however, two requirements:
    # (1) `$x` does not appear in `expr` as a free or bound variable, this is ensured by renaming bound variables in `expr`
    # (2) `$a` does not contain freely any variables that are bound in `%A` (actually only bound at the locations of `$x`)
    [free, bound] = free_bound_vars(expr, kb)
    var_x = token_x.value

    if var_x in free or var_x in bound:
        return    # no combinations possible, since `$x` appears in `expr`, so `sub $x $a %A` is impossible

    ### allow only one subterm to be replaced, much more efficient
    for (cand_expr_a, cand_expr_A) in all_single_hole_decompositions(expr, token_x, kb):
        if expr_a is None  or  equal_expr(expr_a, cand_expr_a, kb):
            if not valid_bindop_conditions(cand_expr_A, kb):
                continue    # e.g. the hole replaced the `∈` of `∀ $k ∈ Nat ...`, not a real subterm
            if bound_var_safe(expr, token_x, cand_expr_a, cand_expr_A, kb):     # requirement (2)
                yield (cand_expr_a, cand_expr_A)

    ### degenerate case the loop above can never produce: `%A` doesn't mention `$x` at all,
    ### so `%A == expr` verbatim and `$a` is completely unconstrained by this equation (`sub
    ### $x $a %A` equals `%A` no matter what `$a` is). `all_single_hole_decompositions` only
    ### ever proposes a `%A` built by replacing some *existing* node of `expr` with `$x` --
    ### it can't propose "no node at all", i.e. `%A = expr` unchanged -- so this case (e.g.
    ### matching `sub $x $a %F` against a concrete `false` when `%F` should just be `false`
    ### itself, needed for `set-comprehension` on a body with zero occurrences of the bound
    ### variable, see doc/kurt-soundness.md #6) was never tried at all. Whatever `expr_a`
    ### already says (a concrete value, or still unconstrained) is carried through unchanged,
    ### since nothing about this candidate depends on `$a`'s value.
    if bound_var_safe(expr, token_x, expr_a, expr, kb):     # requirement (2)
        yield (expr_a, expr)

def all_single_hole_decompositions(expr: Expr, token_x: Token, kb: KnowledgeBase) -> Iterator[tuple[Expr, Expr]]:
    # For each node in expr, yield (node_value, expr_with_that_node_replaced_by_token_x).
    for path, node in iter_nodes(expr):
        yield (node, replace_at_path(expr, path, token_x))
    # each subterm occurring more than once also as one hole at all of its occurrences, e.g. for
    # `n` in `sum x (0, n) x = n * (n + 1) / 2`
    # (not for a bound variable, which would also replace its own binder slot)
    seen: list[Expr] = []
    bound_vars = free_bound_vars(expr, kb)[1] if valid_bindop_conditions(expr, kb) else set()
    for path, node in iter_nodes(expr):
        if len(path) == 0 or any(node == other for other in seen):
            continue
        if isinstance(node, Token) and node.value in bound_vars:
            continue
        seen.append(node)
        if sum(1 for _, other in iter_nodes(expr) if other == node) > 1:
            yield (node, replace_all_occurrences(expr, node, token_x))
    # for each node of a `flat` operator, each group of two or more (but not all) of its
    # arguments as one hole, e.g. `b + c` in `a + b + c + d`: flattening forgot that grouping, but
    # it is still a legitimate subterm (any group, if the operator is also `sym`, otherwise only
    # consecutive arguments) -- last, since most rewriting steps need no group
    for path, node in iter_nodes(expr):
        match node:
            case [Token(label='SYMBOL', value=op), *args] if isinstance(op, str) and len(args) > 2 and kb.is_flat(op):
                for group, rest in flat_groups(args, kb.is_sym(op)):
                    subterm: Expr = [node[0], *group]
                    yield (subterm, replace_at_path(expr, path, token_x, [node[0], *rest]))

def flat_groups(args: list[Expr], sym: bool) -> Iterator[tuple[list[Expr], list[Expr]]]:
    # yield each `(group, rest)` where `group` has two or more but not all of `args`, and `rest`
    # is `args` with `group` replaced by a single `None` placeholder (for the hole)
    n = len(args)
    if sym:
        for k in range(2, n):
            for idx in itertools.combinations(range(n), k):
                group = [args[i] for i in idx]
                rest = [args[i] for i in range(n) if i not in idx] + [None]
                yield group, rest
    else:
        for i in range(n):
            for j in range(i + 2, n + 1):
                if j - i < n:
                    yield args[i:j], args[:i] + [None] + args[j:]

def get_at_path(expr: Expr, path: list[int]) -> Expr:
    """Get the subexpression at the given path."""
    if len(path) == 0:
        return expr
    i = path[0]
    assert isinstance(expr, list) and i < len(expr)
    return get_at_path(expr[i], path[1:])


def replace_at_path(expr: Expr, path: list[int], token_x: Token, node_with_hole: Optional[list] = None) -> Expr:
    """Return a deep copy of expr where the subexpression at `path` is replaced by `token_x`,
    or, if `node_with_hole` is given, by that node with its `None` placeholder replaced by `token_x`."""
    if len(path) == 0:
        if node_with_hole is None:
            return token_x
        return [token_x if e is None else deepcopy_expr(e) for e in node_with_hole]
    i = path[0]
    new_list = deepcopy_expr(expr)
    assert isinstance(new_list, list)
    new_list[i] = replace_at_path(new_list[i], path[1:], token_x, node_with_hole)
    return new_list

def replace_all_occurrences(expr: Expr, subterm: Expr, token_x: Token) -> Expr:
    """Return a deep copy of expr where every occurrence of `subterm` is replaced by `token_x`."""
    if expr == subterm:
        return token_x
    if isinstance(expr, list):
        return [replace_all_occurrences(e, subterm, token_x) for e in expr]
    return expr

def iter_nodes(expr: Expr, path_prefix: list[int]|None = None) -> Iterator[tuple[list[int], Expr]]:
    """Yield (path, subexpression) for every node (including the root)."""
    if path_prefix is None:
        path_prefix = []
    yield path_prefix, expr
    if isinstance(expr, list):
        for i, child in enumerate(expr):
            yield from iter_nodes(child, path_prefix + [i])

def match_against_sub(expr: Expr, pattern: Expr, tail: list[tuple[Expr, Expr]], s: State, kb: KnowledgeBase) -> Iterator[State]:
    # match `expr` against `sub $x a A`, i.e., find the states for which `expr == A[$x := a]`
    # (second-order matching, see `sub_solutions`), and go on with the `tail`
    assert not is_sub(expr)
    assert isinstance(pattern, list) and len(pattern) == 4
    token_sub, token_x, p_a, p_A = pattern
    assert isinstance(token_sub, Token) and token_sub.value == SUB_SYMBOL
    assert isinstance(token_x, Token) and isinstance(token_x.value, str)
    for s_sub in sub_solutions(expr, token_x, p_a, p_A, s, kb):
        yield from unify_exprs_with_patterns(tail, s_sub, kb)

def sub_condition_match(cond_e: Expr, v_e: str, args_e: list[Expr], cond_p: Expr, args_p: list[Expr], tail: list[tuple[Expr, Expr]], s: State, kb: KnowledgeBase) -> Iterator[State]:
    # match a binder of `expr` with the condition `cond_e` on its bound variable `v_e`, e.g.
    # `∀ (y > 0) (P y)`, against a rule's binder `∀ (sub $x $v %C) %P`, which stands for any
    # condition: `$v` is the bound variable, and `%C` is `cond_e` with the hole `$x` for *every*
    # occurrence of the bound variable (`$x > 0`) -- so `%C` never contains the bound variable
    # itself, and the match is unique (no search as for `sub` elsewhere)
    assert isinstance(cond_p, list) and len(cond_p) == 4
    _, token_x, token_v, p_C = cond_p
    assert isinstance(token_x, Token) and isinstance(token_x.value, str)
    assert isinstance(token_v, Token) and isinstance(token_v.value, str)
    x, v_p = token_x.value, token_v.value
    if contains_symbol(cond_e, x) or any(contains_symbol(a, x) for a in args_e):
        return
    C = alpha_rename_binder_body([deepcopy_expr(cond_e)], v_e, x, kb)[0]
    args_r = alpha_rename_binder_body([deepcopy_expr(a) for a in args_e], v_e, v_p, kb)
    s_local = s.block_always(v_p)
    for s_C in unify_exprs_with_patterns([(C, p_C)], s_local.block_as_domain(x), kb):
        yield from unify_exprs_with_patterns(list(zip(args_r, args_p)) + tail, restore_blocked(s_C, x, s_local), kb)

def sub_solutions(expr: Expr, token_x: Token, p_a: Expr, p_A: Expr, s: State, kb: KnowledgeBase) -> Iterator[State]:
    # the states extending `s` with `expr == A[$x := a]` for the pattern parts `a` and `A` --
    # candidates are generated, and each one is then *checked* by computing the substitution
    # (`sub_holds`), so a generator that proposes too much (or something odd) can never make
    # the result unsound, only slower; too little makes it incomplete
    #   1. `A` is fully known, e.g. by the conclusion of "forall-elim": try each subterm of
    #      `expr` (and nothing) as `a`
    #   2. otherwise, e.g. `%A` or `R $x $d`: take `expr` apart, i.e., choose a subterm `a` and
    #      which of its occurrences become the hole `$x` (`generate_all_combinations`), and
    #      match the rest against `A`
    # (`sub`s are never nested, see `check_sub_not_nested`)
    x = token_x.value
    assert isinstance(x, str)
    seen: set[str] = set()
    def checked(s_cand: State) -> Iterator[State]:
        if sub_holds(expr, token_x, p_a, p_A, s_cand, kb):
            key = expr_sexpr(apply_subst([p_a, p_A], s_cand, kb), kb)
            if key not in seen:
                seen.add(key)
                yield s_cand
    def matching_a(candidate: Optional[Expr], s_now: State) -> list[State]:
        if candidate is None:
            return [s_now]      # `$x` doesn't occur, `a` stays whatever it is
        return list(unify_exprs_with_patterns([(candidate, p_a)], s_now, kb))
    A = apply_subst(p_A, s, kb)
    if not contains_unbound_var(A, s, kb, except_var=x):
        for candidate in subterm_candidates(expr, kb):
            for s_a in matching_a(candidate, s):
                yield from checked(s_a)
        return
    a = apply_subst(p_a, s, kb)
    a_value = a if not contains_unbound_var(a, s, kb) else None
    for (cand_a, cand_A) in generate_all_combinations(expr, token_x, a_value, kb):
        for s_a in matching_a(cand_a, s):
            for s_A in unify_exprs_with_patterns([(cand_A, p_A)], s_a.block_as_domain(x), kb):
                yield from checked(restore_blocked(s_A, x, s))

def subterm_candidates(expr: Expr, kb: KnowledgeBase) -> Iterator[Optional[Expr]]:
    # each distinct subterm of `expr`, including groups of arguments of flat operators, and
    # `None` (for "no occurrence at all") -- but none with a variable that `expr` binds: that one
    # is no term outside its binder (found in the soundness review of 2026-09-29)
    try:
        bound = free_bound_vars(expr, kb)[1]
    except KurtException:
        bound = set()
    seen: list[Expr] = []
    for _, node in iter_nodes(expr):
        if isinstance(node, Token):
            if node.value in bound:
                continue
        elif bound and not free_vars_only(node, kb).isdisjoint(bound):
            continue
        if not any(node == other for other in seen):
            seen.append(node)
            yield node
    for _, node in iter_nodes(expr):
        match node:
            case [Token(label='SYMBOL', value=op), *args] if isinstance(op, str) and len(args) > 2 and kb.is_flat(op):
                for group, _ in flat_groups(args, kb.is_sym(op)):
                    yield [node[0], *group]
    yield None

def sub_holds(expr: Expr, token_x: Token, p_a: Expr, p_A: Expr, s: State, kb: KnowledgeBase) -> bool:
    # whether `expr == A[$x := a]` for the values of `a` and `A` in `s`, with the substitution
    # computed exactly like everywhere else (capture-avoiding, then normalized); an `a` without
    # value is fine only if `A` doesn't mention `$x`
    x = token_x.value
    assert isinstance(x, str)
    try:
        A = apply_subst(p_A, s, kb)
        a = apply_subst(p_a, s, kb)
        if contains_unbound_var(A, s, kb, except_var=x):
            return False       # parts still unknown -- nothing to check
        if contains_unbound_var(a, s, kb):      # no value for `a` (a variable of the goal is one)
            if contains_symbol(A, x):
                return False
            result = A
        else:
            result, _ = trigger_sub([Token('SYMBOL', SUB_SYMBOL), token_x, a, A], State.empty(), kb)
        return equal_expr(normalize_expr(result, kb), expr, kb)
    except KurtException:
        return False       # e.g. the hole cut into a binder's condition, not a real subterm

def contains_sub(expr: Expr) -> bool:
    return is_sub(expr) or (isinstance(expr, list) and any(contains_sub(e) for e in expr))

def check_sub_not_nested(expr: Expr) -> None:
    # a `sub` inside the value or the body of another `sub` isn't supported -- a rule about two
    # variables can be applied twice instead, one variable at a time
    if is_sub(expr):
        assert isinstance(expr, list)
        if contains_sub(expr[2]) or contains_sub(expr[3]):
            raise KurtException(f'EvalError: nested `{SUB_SYMBOL}` is not supported -- write a rule for one variable, and apply it once per variable')
    if isinstance(expr, list):
        for e in expr:
            check_sub_not_nested(e)

def check_condition_holes(expr: Expr, kb: KnowledgeBase) -> None:
    # a rule's binder with any condition, `∀ (sub $x $v %C) %P`: the condition `%C` has the
    # hole `$x`, so it may only be used with something substituted for `$x`, as `sub $x ... %C`
    # -- on its own it would mention the rule's `$x`
    holes: dict[str, str] = {}
    def binder_slots(e: Expr) -> None:
        match e:
            case [Token(label='SYMBOL', value=op), cond, *_] if isinstance(op, str) and op != SUB_SYMBOL and kb.is_bindop(op) and is_sub(cond):
                assert isinstance(cond, list)
                x, C = cond[1], cond[3]
                if isinstance(x, Token) and isinstance(C, Token) and is_bool_var_token(C, kb):
                    assert isinstance(x.value, str) and isinstance(C.value, str)
                    if holes.setdefault(C.value, x.value) != x.value:
                        raise KurtException(f'EvalError: the condition `{C.value}` must always have the same hole `{holes[C.value]}`')
        if isinstance(e, list):
            for c in e:
                binder_slots(c)
    def check(e: Expr) -> None:
        if isinstance(e, Token):
            if isinstance(e.value, str) and e.value in holes:
                raise KurtException(f'EvalError: the condition `{e.value}` of a binder can only be used as `{SUB_SYMBOL} {holes[e.value]} ... {e.value}`')
            return
        if is_sub(e):
            x, C = e[1], e[3]
            if isinstance(C, Token) and isinstance(C.value, str) and C.value in holes:
                if not (isinstance(x, Token) and x.value == holes[C.value]):
                    raise KurtException(f'EvalError: the condition `{C.value}` must always have the same hole `{holes[C.value]}`')
                check(e[2])
                return
        for c in e:
            check(c)
    binder_slots(expr)
    if holes:
        check(expr)

def contains_unbound_var(expr: Expr, s: State, kb: KnowledgeBase, except_var: Optional[str] = None, bound: frozenset[str] = frozenset()) -> bool:
    # whether `expr` has a free variable without value in `s` (other than `except_var`)
    e = s.walk(expr)
    match e:
        case Token():
            # (a free variable of the goal itself is blocked as domain: it is fixed, not unknown)
            return (is_var_token(e, kb) and e.value != except_var and e.value not in bound
                    and not s.is_blocked_as_domain(e.value))
        case [Token(label='SYMBOL', value=op), cond, *_] if isinstance(op, str) and kb.is_bindop(op):
            try:
                bv, _ = unpack_condition(cond, kb)
            except KurtException:
                return True
            return any(contains_unbound_var(c, s, kb, except_var, bound | {bv}) for c in e)
        case [*children]:
            return any(contains_unbound_var(c, s, kb, except_var, bound) for c in children)
    return False

def restore_blocked(s_new: State, x: str, s_old: State) -> State:
    # undo the temporary blocking of `$x` (unless it was blocked before)
    if x in s_old.blocked_as_domain:
        return s_new
    return State(s_new.subst, s_new.blocked_as_domain - {x}, s_new.blocked_as_range, s_new.eigen)

# A non-boolean schema variable `$T` in the body of a binder over `$i` normally stands for a
# term that does *not* depend on `$i` -- e.g. in `(forall $x ($x = $T)) and (P $T) implies Q`,
# `$T` is one fixed term, and letting it capture `$x` would change what the axiom says. But if
# every occurrence of `$T` is inside a binder over `$i`, or is the body of a `sub $i ... $T`,
# the axiom only ever uses `$T` for the bound `$i` or with something substituted for it, as in
# `(sum $i ($a, $a) $T) = sub $i $a $T` -- then `$T` may depend on `$i`. `dependent_vars` maps
# each such (renamed, so globally unique) `$T` to its `$i`.
dependent_vars: dict[str, str] = {}

def find_dependent_vars(expr: Expr, kb: KnowledgeBase) -> dict[str, str]:
    # the non-boolean schema variables of `expr` that may depend on a bound variable: those that
    # only ever occur as the *whole* body of a binder over the same `$i` (`sum $i ($a, $b) $T`)
    # or of a `sub $i ... $T` -- being just somewhere inside a binder's scope isn't enough, e.g.
    # the `$x` in `exists $y (not ($x = $y))` must stay independent of `$y`
    occurrences: dict[str, list[Optional[tuple[str, bool]]]] = {}   # var -> (binder, is a `sub`), or None
    def note(e: Expr, context: Optional[tuple[str, bool]]) -> bool:
        if isinstance(e, Token) and isinstance(e.value, str) and e.value.startswith('$') and kb.is_var(e.value) and not kb.is_bool(e.value):
            occurrences.setdefault(e.value, []).append(context)
            return True
        return False
    def walk(e: Expr) -> None:
        match e:
            case Token():
                note(e, None)
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=bv), a, A] if op == SUB_SYMBOL and isinstance(bv, str):
                walk(a)
                if not note(A, (bv, True)):
                    walk(A)
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                try:
                    bv, _ = unpack_condition(cond, kb)
                except KurtException:
                    return
                walk(cond)
                for child in body[:-1]:
                    walk(child)
                if body and not note(body[-1], (bv, False)):
                    walk(body[-1])
            case [*children]:
                for child in children:
                    walk(child)
    walk(expr)
    result: dict[str, str] = {}
    for v, contexts in occurrences.items():
        binders = {c[0] for c in contexts if c is not None}
        if None not in contexts and len(binders) == 1 and any(not c[1] for c in contexts if c is not None):
            result[v] = binders.pop()
    return result

def may_capture(v: str, expr: Expr, s: State) -> bool:
    # whether the schema variable `v` may take the value `expr`, which contains a bound variable
    # (blocked as range): only a dependent variable, and only its own bound variable
    b = dependent_vars.get(v)
    return b is not None and blocked_range_vars(expr, s) <= {b}

def blocked_range_vars(expr: Expr, s: State) -> set[str]:
    if isinstance(expr, Token):
        return {expr.value} if isinstance(expr.value, str) and s.is_blocked_as_range(expr.value) else set()
    return set().union(*(blocked_range_vars(e, s) for e in expr)) if expr else set()

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
    # can be either boolean or non-boolean
    if not (isinstance(e, Token) and e.label == 'SYMBOL'):
        return False
    assert isinstance(e.value, str)
    return kb.is_var(e.value)

def is_bool_var_token(e:Expr, kb) -> bool:
    if not (isinstance(e, Token) and e.label == 'SYMBOL'):
        return False
    assert isinstance(e.value, str)
    return kb.is_var(e.value) and kb.is_bool(e.value)

# the non-recursive calls are having a single expr and a single pattern, the recursive calls then might have more
# each "case" with a recursive call loops over all generated local substitutions
# `exprs_patterns`:   [(e1, p1), (e2, p2), ...] = zip([e1, e2, ...], [p1, p2, ...])
# this list is necessary for the `[*_]` case, i.e., for matching two lists
# `two_sided` means that variables in the exprs can also be assigned
def has_computation(e: Expr, kb: 'KnowledgeBase') -> bool:
    # whether `calc` has something to compute in `e`: an operation of the calculator with two
    # numbers (or with one, like `- 3`) -- a quick test before computing
    if isinstance(e, Token):
        return False
    ops = kb.get_calc_ops(e[0].value) if e and isinstance(e[0], Token) and isinstance(e[0].value, str) else []
    if ops:
        values = [v for v in (number_value(a, kb) for a in e[1:]) if v is not None]
        if len(values) >= 2 or (len(values) == 1 and len(e) == 2):
            return True         # (not `0 + x` or `1 * x`: rules like "add-identity" are full of those)
    return any(has_computation(c, kb) for c in e[1:])

def computes_to(pattern: Expr, expr: Expr, s: State, kb: KnowledgeBase) -> bool:
    # with `calc on`: whether `pattern`, an arithmetic expression whose variables all have values
    # in `s`, computes to `expr` (a step the kernel checks again, see `k_instance`)
    if not (kb.calc and isinstance(pattern, list) and pattern and isinstance(pattern[0], Token) and isinstance(pattern[0].value, str)
            and any(op in CALCULATOR_OPERATIONS for op in kb.get_calc_ops(pattern[0].value))):   # operations, not comparisons
        return False
    if is_var_token(expr, kb):
        return False        # a variable is matched by binding it, not by computing
    instance = apply_subst(pattern, s, kb)
    if not has_computation(instance, kb) or contains_unbound_var(instance, s, kb):
        return False
    computed = calculate_normalized(instance, kb)
    return not equal_expr(computed, instance, kb) and equal_expr(computed, expr, kb)   # (`expr` is computed already, as typed or stored)

def unify_exprs_with_patterns(exprs_patterns: list[tuple[Expr, Expr]], s: State, kb: KnowledgeBase) -> Iterator[State]:

    if len(exprs_patterns) == 0:
        yield s     # we emptied the matching tasks and found a substitution
    else:
        [(expr, pattern), *tail] = exprs_patterns   # unpack

        # lazy style: apply `walk` before processing, i.e., apply the substitution
        # (alternative: eager style: apply `walk` to the tail after each change to the substitution)
        expr = s.walk(expr)
        pattern = s.walk(pattern)

        if equal_expr(expr, pattern, kb):
            # equal, just continue with the `tail`
            yield from unify_exprs_with_patterns(tail, s, kb)

        elif computes_to(pattern, expr, s, kb):
            # `calc on`: an arithmetic part of the rule, whose variables all have values by now,
            # computes to `expr`, e.g. `$x * $x` with `$x := 3` matches `9`
            yield from unify_exprs_with_patterns(tail, s, kb)

        elif is_var_token(pattern, kb) or is_var_token(expr, kb):
            if is_var_token(pattern, kb):
                # `pattern` is a variable (maybe `expr` as well)
                assert isinstance(pattern, Token) and isinstance(pattern.value, str)
                v = pattern.value
                assert s.lookup(v) is None
                bp = kb.is_bool(v)
                be = bool_expr(expr, kb)
                if ((bp and be) or (not bp and not be and (not s.contains_blocked_as_range(expr) or may_capture(v, expr, s)) and not s.contains_eigen(expr))):
                    if not s.occurs(v, expr) and not s.is_blocked_as_domain(v):
                        # we can safely assign `v` without creating infinite substitutions
                        s = s.bind(v, expr)   # extend the substitution
                        yield from unify_exprs_with_patterns(tail, s, kb)

            if is_var_token(expr, kb):
                # `expr` is a variable (maybe `pattern` as well)
                assert isinstance(expr, Token) and isinstance(expr.value, str)
                u = expr.value
                assert s.lookup(u) is None
                be = kb.is_bool(u)
                bp = bool_expr(expr, kb)
                if ((bp and be) or (not bp and not be and (not s.contains_blocked_as_range(pattern) or may_capture(u, pattern, s)))):
                    if not s.occurs(u, pattern) and not s.is_blocked_as_domain(u):
                        # we can safely assign `u` without creating infinite substitutions
                        s = s.bind(u, pattern)   # extend the substitution
                        yield from unify_exprs_with_patterns(tail, s, kb)

        else:
            # branch on `pattern` for unification
            match pattern:

                # an operator that is a variable, e.g. the `∘` of group.kurt: once it has a value,
                # e.g. `+`, match with the rules of that operator (`flat`, `sym`)
                case [Token(label='SYMBOL', value=op_p) as head_p, *args_p] if (isinstance(op_p, str) and kb.is_var(op_p)
                        and isinstance(expr, list) and len(expr) > 0 and isinstance(expr[0], Token)
                        and isinstance(expr[0].value, str) and (kb.is_flat(expr[0].value) or kb.is_sym(expr[0].value))):
                    for s_head in unify_exprs_with_patterns([(expr[0], head_p)], s, kb):
                        bound_head = s_head.walk(head_p)
                        if bound_head is not head_p:
                            yield from unify_exprs_with_patterns([(expr, [bound_head, *args_p])] + tail, s_head, kb)

                # binding operator matching (rename bound variable before!)
                case [Token(label='SYMBOL', value=op_p), cond_p, *args_p] if isinstance(op_p, str) and kb.is_bindop(op_p):
                    v_p, opt_condition_p = unpack_condition(cond_p, kb)
                    if op_p == SUB_SYMBOL and not is_sub(expr):   
                            # asymmetric:  don't match a `sub` expr to a `sub` pattern (an infinite loop!)
                            yield from match_against_sub(expr, pattern, tail, s, kb)
                    # in any case: additionally binding ops match against their matching binding ops
                    match expr:
                        case [Token(label='SYMBOL', value=op_e), cond_e, *args_e] if isinstance(op_e, str) and kb.is_bindop(op_e):
                            v_e, opt_condition_e = unpack_condition(cond_e, kb)
                            if op_p==op_e and len(args_p)==len(args_e) and is_sub(cond_p) and opt_condition_e is not None and not is_sub(cond_e):
                                # a rule's binder with any condition, e.g. `∀ (sub $x $v %C) %P`
                                yield from sub_condition_match(cond_e, v_e, args_e, cond_p, args_p, tail, s, kb)
                            elif op_p==op_e and len(args_p)==len(args_e) and ((opt_condition_p is None) == (opt_condition_e is None)):
                                assert isinstance(v_p, str) and isinstance(v_e, str)
                                if opt_condition_e is not None:
                                    assert isinstance(cond_e, list) and isinstance(cond_p, list)
                                    args_e = args_e + cond_e
                                    args_p = args_p + cond_p
                                # Rename the expr-side binder body from v_e to v_p (alpha-eq) before unifying --
                                # unless `v_p` is free there, which the renaming would capture: then the pattern's
                                # binder (which shadows `v_p`) and the expr's can't be the same, e.g. `∀ $x (Q $x $x)`
                                # and `∀ $z (Q $x $z)` (found in the soundness review of 2026-09-29)
                                if v_p != v_e and any(v_p in free_vars_only(a, kb) for a in args_e):
                                    return
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

                # list matching (same length, no special operators) -- not of a binder (its bound
                # variable is no argument), which an operator variable `∘` could otherwise match
                case [*_] if isinstance(expr, list) and len(expr)==len(pattern) and not (
                        isinstance(expr[0], Token) and isinstance(expr[0].value, str) and kb.is_bindop(expr[0].value)):
                    yield from unify_exprs_with_patterns(list(zip(expr, pattern)) + tail, s, kb)

                case _:
                    # we didn't match the pattern, so we cannot extend the substitution
                    pass

        
def free_vars_only(e: Expr, kb: KnowledgeBase) -> set[str]:
    return free_bound_vars(e, kb)[0]

def alpha_rename_binder_body(body: list[Expr], old: str, new: str, kb: KnowledgeBase) -> list[Expr]:
    # rename bound occurrences of `old` to `new` *inside this binder body only*.
    # stop if we encounter an inner binder that also binds `old`.
    def ren(e: Expr) -> Expr:
        match e:
            case Token(label='SYMBOL', value=s) if isinstance(s, str) and s == old:
                # This occurrence is bound by the current binder thus rename
                return Token(label='SYMBOL', value=new)
            case [Token(label='SYMBOL', value=op), cond, *tail] if isinstance(op, str) and kb.is_bindop(op):
                bv, opt_condition = unpack_condition(cond, kb)
                if bv == old:
                    # A new binder that *rebinds* `old` thus do not rename under it
                    return [Token(label='SYMBOL', value=op), cond, *tail]
                # Otherwise, keep renaming under this binder
                return [Token(label='SYMBOL', value=op), ren(cond), *[ren(c) for c in tail]]
            case [*children]:
                return [ren(c) for c in children]
            case _:
                return e
    return [ren(c) for c in body]

def fresh_like(name: str, avoid: set[str], kb: KnowledgeBase) -> str:
    # make a fresh variable name of the same sort as `name` not in `avoid`.
    # uses your generators; ensure kb treats them as variables.
    if kb.is_bool(name):
        while True:
            cand = new_bool_var_name(name)
            if cand not in avoid: return cand
    else:
        while True:
            cand = new_var_name(name)
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

            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                bv, opt_condition = unpack_condition(cond, kb)

                # if this binder binds x, x is not free below thus no substitution under it,
                # but we still recurse structurally to catch nested binders that might need α-renaming
                if bv == x:
                    new_body = [go(c, blk | {bv}) for c in body]
                    return [Token(label='SYMBOL', value=op), cond, *new_body]

                # if bv occurs free in t, α-rename this binder locally
                if bv in FVt:
                    # Build an avoid set to keep name fresh w.r.t. t and current e
                    avoid = FVt | free_vars_only([Token(label='SYMBOL', value=op), cond, *body], kb) | {x} | set(blk)
                    bv2 = fresh_like(bv, avoid, kb)
                    cond_ren = alpha_rename_binder_body([cond], bv, bv2, kb)[0]
                    body_ren = alpha_rename_binder_body(body, bv, bv2, kb)
                    new_body = [go(c, blk | {bv2}) for c in body_ren]
                    return [Token(label='SYMBOL', value=op), cond_ren, *new_body]
                # Normal descent: no α-renaming needed
                new_cond = go(cond, blk | {bv})
                new_body = [go(c, blk | {bv}) for c in body]
                return [Token(label='SYMBOL', value=op), new_cond, *new_body]

            case [*children]:
                return [go(c, blk) for c in children]

        return e

    # 1) α-rename binders in A that would capture free vars of t
    A_alpha = go(A, s.blocked_as_domain)

    # 2) now do the capture-avoiding replacement using your apply_subst
    #    (blocked prevents touching bound occurrences of x)
    return apply_subst(A_alpha, s.bind(x, t), kb)

# trigger a single substitution in `expr` if possible, return the new expression and the new state
class BinderMisread(KurtException):
    # a rule's binder `∀ (sub $x $v %C) ...` whose condition, once computed, binds another variable
    # than `$v`: `∀ ($y > $v) P $y` reads as a binder over `$y` -- the search skips such a match
    def __init__(self) -> None:
        super().__init__('EvalError: the condition of a binder binds another variable once computed')

def trigger_sub(expr: Expr, s: State, kb: KnowledgeBase) -> tuple[Expr, State]:
    expr = deepcopy_expr(expr)
    # fully apply current substitution (capture-avoiding via blocked)
    expr = apply_subst(expr, s, kb)

    def unblock_as_before(s_new: State, x: str, s_old: State) -> State:
        # leave the scope of `x`: unblock it -- but a free variable of the goal (blocked as domain
        # only, see `impl_elim`) stays blocked: a bound and a free variable can have the same name
        # (found in the soundness review of 2026-09-29). A block as domain *and* range is the one of
        # a rule's binder from matching (`block_always`), which ends here.
        s_new = State(s_new.subst, s_new.blocked_as_domain - {x}, s_new.blocked_as_range - {x}, s_new.eigen)
        if x in s_old.blocked_as_domain and x not in s_old.blocked_as_range:
            s_new = s_new.block_as_domain(x)
        return s_new

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
                if not is_bool_var_token(A_s, kb) or (isinstance(A_s, Token) and x == A_s.value):
                    # we're done with the binder x; unblock it BEFORE returning
                    s_after = unblock_as_before(s_local, x, s)
                    # perform capture-avoiding A[x:=t]
                    A_repl = capture_avoiding_replace(A_s, x, t_s, s_after, kb)
                    # e.g. `b + c` replacing `$x` in `a + $x` must give the flat `a + b + c`
                    A_repl = normalize_expr(A_repl, kb)
                    return A_repl, s_after
                else:
                    # do NOT leave x permanently blocked if we don't fire
                    s_after = unblock_as_before(s_local, x, s)
                    return [e[0], e[1], t_s, A_s], s_after

            # binding operator: [op, bv, *body]
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                bv, opt_condition = unpack_condition(cond, kb)

                # enter binder scope
                s_scope = s.block_always(bv)
                new_cond, s_scope = trigger_sub_core(cond, s_scope)
                if is_sub(cond) and not is_sub(new_cond):
                    try:
                        reading = unpack_condition(new_cond, kb)[0]
                    except KurtException:
                        reading = None        # no variable to bind at all
                    if reading != bv:
                        raise BinderMisread()     # found in the soundness review of 2026-09-29
                new_body, s_scope = trigger_sub_core(body, s_scope)
                # leave binder scope (pop the block)
                s_after = unblock_as_before(s_scope, bv, s)
                assert isinstance(new_body, list)
                return [e[0], new_cond, *new_body], s_after

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

################################
## certificates for the kernel ##
################################
# The search above (unification, `sub` matching, stripping quantifiers, blocked and eigen
# variables, ...) is not trusted: for every step it finds, it hands a *certificate* to the
# kernel below, which checks the step again on its own -- by substituting the values into the
# rule, and comparing the result with the goal and the facts, without any search.

@dataclass
class Certificate:
    kind: str                           # 'rule', or 'top', 'calc', 'calc-fact', 'todo', or a block rule (see `block`)
    goal: Expr                          # the claim, as `derive_expr` sees it (outer `∀`s removed, variables renamed)
    fixed: frozenset[str]               # the free variables of the goal, which stand for anything: they get no value
    rule: Optional[Formula] = None      # the fact or rule used ('rule'), or the fact that computes to the goal ('calc-fact')
    form: str = ''                      # how the rule is read: 'fact' (the goal is an instance) or 'impl' (premise ⇒ conclusion)
    expr: Optional[Expr] = None         # the rule as read: its `simplified_expr`, or one direction `L ⇒ R` of an `iff`
    premise_fresh: tuple[str, ...] = () # the fresh names for the outer `∀`s of the premise, in order
    conclusion_fresh: tuple[str, ...] = ()  # ... and for those of the conclusion
    values: dict[str, Expr] = field(default_factory=dict)   # the values of the variables (of the rule and of the facts)
    facts: list[Formula] = field(default_factory=list)      # the facts that match the parts of the premise
    fact_fresh: list[tuple[str, ...]] = field(default_factory=list)  # fresh names for `∀` parts of the premise, matched without their `∀`s
    block: Optional[KnowledgeBase] = None   # for closing a block ('impl-intro', 'not-intro', 'forall-intro', 'exists-elim'): its level

    def short(self, filename: str, mainstream: bool) -> str:
        # the reason Kurt prints for a step: the rule applied to the facts, e.g.
        # `by equal-elim(11, 10)`, `by 2(3)` (the implication of line 2 with the fact of line 3),
        # `by forall-intro(13-14)` (the lines of the block) -- `cert` shows the long form
        def ref(f: Formula) -> str:
            if f.label:
                return f.label
            return f.line if mainstream and f.filename == filename else f'{os.path.basename(f.filename)}:{f.line}'
        match self.kind:
            case 'rule':
                assert self.rule is not None
                if self.form == 'fact':
                    return f'by {ref(self.rule)}'
                return f'by {ref(self.rule)}({", ".join(ref(f) for f in self.facts)})'
            case 'top':
                return 'by top-intro'
            case 'calc':
                return 'by calc'
            case 'calc-fact':
                assert self.rule is not None
                return f'by calc({ref(self.rule)})'
            case 'todo':
                return 'by todo'
        assert self.block is not None and self.rule is not None
        first = self.block.theory[0].line if self.block.theory else self.rule.line
        lines = first if first == self.rule.line else f'{first}-{self.rule.line}'
        if self.kind == 'exists-elim' and self.block.pick_source is not None:
            return f'by exists-elim({ref(self.block.pick_source)}, {lines})'
        return f'by {self.kind}({lines})'

class KernelError(KurtException):
    # the kernel rejects a step that the search accepted: the two disagree, which is a bug in one
    # of them -- the step doesn't count. Its kind `KernelError` isn't one an `expect` can name, so
    # it always stops a file (in the shell, only the line fails).
    def __init__(self, msg: str) -> None:
        super().__init__(msg, kind='KernelError')

# the certificates of each line (file name, line number), with the kernel's verdict -- for `cert`
certificates_by_line: dict[tuple[str, int], list[tuple[Certificate, Optional[str]]]] = {}
current_line: list[Optional[tuple[str, int]]] = [None]      # the line being evaluated (see `scan_parse_check_eval`)

def record_certificate(cert: Certificate, kb: KnowledgeBase) -> Certificate:
    # the kernel checks every step; `cert` shows the certificates of a line
    try:
        problem = kernel_verify(cert, kb)
    except Exception as e:      # a crash of the kernel counts as a rejection
        problem = f'the kernel failed: {type(e).__name__}: {e}'
    if problem is not None:
        raise KernelError(f'KernelError: the kernel rejects the step to `{expr_str(cert.goal, kb)}`: {problem} -- '
                          f'the search accepted it, so this is a bug in Kurt; please report it, with this file')
    if current_line[0] is not None:
        certificates_by_line.setdefault(current_line[0], []).append((cert, problem))
    return cert

def formula_place(f: Formula, filename: str) -> str:
    # where a formula comes from, e.g. `line 3` or `logic.kurt:22 "forall-elim"`
    place = f'line {f.line}' if f.filename == filename else f'{os.path.basename(f.filename)}:{f.line}'
    return place + (f' "{f.label}"' if f.label else '')

def is_internal_name(v: Value) -> bool:
    return isinstance(v, str) and (v.startswith('$$') or v.startswith('%%')) and v[2:].isdigit()

def readable_names(exprs: list[Expr]) -> dict[str, str]:
    # a name for each internal variable in `exprs`: the one it stands for (`origin_names`),
    # numbered where several stand for the same one, and never a name that `exprs` already use
    internal: list[str] = []
    taken: set[str] = set()
    def walk(e: Expr) -> None:
        if isinstance(e, Token):
            if is_internal_name(e.value):
                if e.value not in internal:
                    internal.append(str(e.value))
            elif isinstance(e.value, str):
                taken.add(e.value)
        else:
            for c in e:
                walk(c)
    for e in exprs:
        walk(e)
    def base(v: str) -> str:
        b = origin_names.get(v, v)
        return b if not is_internal_name(b) else ('%A' if v.startswith('%') else '$v')
    counts: dict[str, int] = {}
    for v in internal:
        counts[base(v)] = counts.get(base(v), 0) + 1
    names: dict[str, str] = {}
    numbers: dict[str, int] = {}
    for v in internal:
        b = base(v)
        name = b
        if counts[b] > 1 or b in taken:
            while True:
                numbers[b] = numbers.get(b, 0) + 1
                name = f'{b}{numbers[b]}'
                if name not in taken:
                    break
        taken.add(name)
        names[v] = name
    return names

def rename_for_display(e: Expr, names: dict[str, str]) -> Expr:
    if isinstance(e, Token):
        return Token('SYMBOL', names[e.value]) if isinstance(e.value, str) and e.value in names else e
    return [rename_for_display(c, names) for c in e]

def certificate_str(cert: Certificate, problem: Optional[str], kb: KnowledgeBase, filename: str) -> str:
    # a certificate in long form, as comment lines -- with the names of the variables as written
    shown: list[Expr] = [cert.goal]
    if cert.expr is not None:
        shown.append(cert.expr)
    shown += list(cert.values.values()) + [f.simplified_expr for f in cert.facts]
    shown += [Token('SYMBOL', v) for v in list(cert.values) + list(cert.fixed) + list(cert.premise_fresh) + list(cert.conclusion_fresh)]
    shown += [Token('SYMBOL', v) for names in cert.fact_fresh for v in names]
    names = readable_names(shown)
    def n(v: str) -> str:
        return names.get(v, v)
    def e(x: Expr) -> str:
        return f'`{expr_str(rename_for_display(x, names), kb)}`'
    lines = [f'goal:      {e(cert.goal)}']
    if cert.fixed:
        lines.append(f'           (with {", ".join(sorted(n(v) for v in cert.fixed))} for anything)')
    match cert.kind:
        case 'top':
            lines.append('by:        "top-intro"')
        case 'calc':
            lines.append('by:        calc, computing the comparison')
        case 'calc-fact':
            assert cert.rule is not None
            lines.append(f'by:        calc, from {e(cert.rule.expr)} ({formula_place(cert.rule, filename)}), which computes to the goal')
        case 'todo':
            lines.append('by:        `todo`, not checked')
        case 'impl-intro' | 'not-intro' | 'forall-intro' | 'exists-elim':
            block = cert.block
            assert block is not None and cert.rule is not None
            opened = f'`{block.mode_str} {", ".join(expr_str(a, kb) for a in block.mode_args)}`'
            lines.append(f'by:        "{cert.kind}", closing the block {opened}')
            if cert.kind == 'exists-elim' and block.pick_source is not None and block.pick_fact is not None:
                lines.append(f'picked:    {e(block.pick_fact.expr)} from {e(block.pick_source.expr)} ({formula_place(block.pick_source, filename)})')
            lines.append(f'last line: {e(cert.rule.expr)} ({formula_place(cert.rule, filename)})')
        case 'rule':
            assert cert.rule is not None and cert.expr is not None
            # the rule and the facts with the internal names of their variables, which the values use
            place = formula_place(cert.rule, filename)
            if cert.rule.direction_of is not None:
                lines.append(f'rule:      {e(cert.expr)}, one direction of {e(cert.rule.direction_of)} ({place})')
            else:
                lines.append(f'rule:      {e(cert.expr)} ({place})')
            if cert.form == 'fact':
                lines.append('read as:   a fact, the goal is an instance of it')
            else:
                lines.append('read as:   premise ⇒ conclusion')
                if cert.premise_fresh:
                    lines.append(f'           the `∀` of the premise with the fresh {", ".join(n(v) for v in cert.premise_fresh)}, which get no value')
                if cert.conclusion_fresh:
                    lines.append(f'           the `∀` of the conclusion with {", ".join(n(v) for v in cert.conclusion_fresh)}')
            for i, (v, value) in enumerate(sorted(cert.values.items(), key=lambda kv: n(kv[0]))):
                lines.append(f'{"values:" if i == 0 else "":11s}{n(v)} := {e(value)}')
            for i, f in enumerate(cert.facts):
                lines.append(f'{"premise:" if i == 0 else "":11s}{e(f.simplified_expr)} ({formula_place(f, filename)})')
            for fresh in cert.fact_fresh:
                lines.append(f'           a `∀` of the premise with the fresh {", ".join(n(v) for v in fresh)}')
    lines.append('kernel:    checked' if problem is None else f'kernel:    REJECTED -- {problem}')
    return '\n'.join('; ' + line for line in lines)

###################################################
## `.kurtc` files: the certificates of a file ##
###################################################
# After a file checks (without errors and `todo`s), its certificates are written to `foo.kurtc`
# next to `foo.kurt`. When the file is loaded again, unchanged, each claim first tries its stored
# certificate: rebuilt against the facts as they are now, and checked by the kernel -- only if
# that fails, the search runs. So a `.kurtc` is only a hint: a wrong or outdated one costs time,
# but can never get a step accepted that the kernel doesn't check. Internal names (`$$07`) are
# different in every run: the file uses canonical names (`$$c0`), mapped back by aligning the
# stored goal, rule and facts with the current ones.

KURTC_VERSION = 1
kurtc_enabled: bool = False       # write and use `.kurtc` files (`kurt` on the command line does)
replay_hints: dict[str, dict[int, list[dict]]] = {}      # file -> line -> its stored certificates
load_dependencies: dict[str, list[str]] = {}              # file -> the files it loads

def source_hash(fname: str) -> Optional[str]:
    try:
        with open(fname, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest() if hashlib is not None else None
    except OSError:
        return None

def expr_to_json(e: Expr, names: dict[str, str]) -> object:
    # an expression as JSON, with the internal names replaced by canonical ones (`names`)
    if isinstance(e, Token):
        v = e.value
        if is_internal_name(v):
            assert isinstance(v, str)
            v = names.setdefault(v, f'{v[:2]}c{len(names)}')
        if isinstance(v, Fraction):
            return [e.label, {'fraction': str(v)}]
        return [e.label, v]
    return {'e': [expr_to_json(c, names) for c in e]}

def expr_from_json(j: object) -> Expr:
    if isinstance(j, dict):
        return [expr_from_json(c) for c in j['e']]
    assert isinstance(j, list) and len(j) == 2
    if isinstance(j[1], dict):
        return Token(j[0], Fraction(j[1]['fraction']))
    return Token(j[0], j[1])

def formula_to_json(f: Formula, names: dict[str, str]) -> dict:
    # how to find `f` again: its file, line, label, and (to tell apart the formulas of a line) its
    # formula -- for one direction of an `iff`, the `iff` and the direction
    if f.direction_of is not None:
        e = f.simplified_expr
        direction = 'lr' if isinstance(e, list) and e[1] is f.direction_of[1] else 'rl'   # type: ignore[index]
        source = f.direction_of
    else:
        direction, source = None, f.simplified_expr
    return {'file': f.filename, 'line': f.line, 'label': f.label, 'direction': direction,
            'expr': expr_to_json(source, names)}

def certificate_to_json(cert: Certificate) -> dict:
    assert cert.kind == 'rule' and cert.rule is not None and cert.expr is not None
    names: dict[str, str] = {}
    return {
        'goal': expr_to_json(cert.goal, names),
        'rule': formula_to_json(cert.rule, names),
        'form': cert.form,
        'facts': [formula_to_json(f, names) for f in cert.facts],
        'premise_fresh': [names.setdefault(v, f'{v[:2]}c{len(names)}') for v in cert.premise_fresh],
        'conclusion_fresh': [names.setdefault(v, f'{v[:2]}c{len(names)}') for v in cert.conclusion_fresh],
        'fact_fresh': [[names.setdefault(v, f'{v[:2]}c{len(names)}') for v in fresh] for fresh in cert.fact_fresh],
        'values': [[names.setdefault(v, f'{v[:2]}c{len(names)}'), expr_to_json(value, names)] for v, value in cert.values.items()],
    }

def write_kurtc(fname: str) -> None:
    # the certificates of the claims of `fname`, by line (block closings and `calc` need none)
    steps: dict[str, list[dict]] = {}
    for (f, line), certs in certificates_by_line.items():
        if f == fname:
            rules = [certificate_to_json(c) for c, _ in certs if c.kind == 'rule']
            if rules:
                steps[str(line)] = rules
    content = {'kurtc': KURTC_VERSION, 'kurt': file_fingerprint(), 'source': os.path.basename(fname),
               'sha256': source_hash(fname),
               'depends': [{'file': d, 'sha256': source_hash(d)} for d in load_dependencies.get(fname, [])],
               'steps': steps}
    try:
        with open(fname + 'c', 'w', encoding='utf-8') as out:
            json.dump(content, out, ensure_ascii=False, separators=(',', ':'))
    except OSError:
        pass        # e.g. a directory without write access: no `.kurtc`, nothing else changes

def read_kurtc(fname: str) -> None:
    # the stored certificates of `fname`, if its `.kurtc` belongs to the file as it is now
    replay_hints.pop(fname, None)
    try:
        with open(fname + 'c', encoding='utf-8') as f:
            content = json.load(f)
    except (OSError, ValueError):
        return
    if not isinstance(content, dict) or content.get('kurtc') != KURTC_VERSION or content.get('sha256') != source_hash(fname):
        return
    try:
        replay_hints[fname] = {int(line): list(certs) for line, certs in content['steps'].items()}
    except (KeyError, ValueError, AttributeError, TypeError):
        replay_hints.pop(fname, None)

def resolve_load(name: str, from_file: str) -> Optional[str]:
    # the file that `load name` in `from_file` loads (as `load_file` finds it), or `None`
    if not name.endswith('.kurt'):
        name += '.kurt'
    paths = packaged_theory_paths if packaged_theory_file(name) is not None else [Path(from_file).parent.resolve()] + theory_path
    for path in paths:
        candidate = path / name
        try:
            if candidate.is_file():
                return str(candidate)
        except (OSError, AttributeError):
            continue
    return None

def loaded_files(fname: str) -> list[str]:
    # the files that the `load` lines of `fname` load (read from the text, without running it)
    found: list[str] = []
    try:
        with open(fname, encoding='utf-8') as f:
            lines = f.readlines()
    except OSError:
        return found
    for line in lines:
        m = re.match(r'\s*load\s+(.*?)\s*(;.*)?$', line)
        if m:
            for name in split_filenames(m.group(1)):
                resolved = resolve_load(name, fname)
                if resolved is not None and resolved not in found:
                    found.append(resolved)
    return found

def kurtc_status(fname: str) -> str:
    # whether `fname` has certificates that fit it as it is now
    try:
        with open(fname + 'c', encoding='utf-8') as f:
            content = json.load(f)
    except OSError:
        return 'not certified'
    except ValueError:
        return 'not certified (the `.kurtc` is damaged)'
    if not isinstance(content, dict) or content.get('kurtc') != KURTC_VERSION:
        return 'not certified (a `.kurtc` of another format)'
    if content.get('sha256') != source_hash(fname):
        return 'out of date: the file changed since'
    changed = [os.path.basename(d.get('file', '?')) for d in content.get('depends', []) if d.get('sha256') != source_hash(d.get('file', ''))]
    note = f', but {", ".join(changed)} changed since' if changed else ''
    if content.get('kurt') != file_fingerprint():
        note += f', by another version of Kurt ({content.get("kurt")})'
    return 'certified' + note

def dependencies_str(fname: str) -> str:
    # the tree of the files that `fname` loads, with the state of their certificates
    lines: list[str] = []
    seen: set[str] = set()
    def date(path: str) -> str:
        try:
            return time.strftime('%Y-%m-%d %H:%M', time.localtime(os.path.getmtime(path)))
        except OSError:
            return '-'
    def show(f: str, prefix: str, last: bool, top: bool) -> None:
        branch = '' if top else ('└─ ' if last else '├─ ')
        name = os.path.basename(f)
        if f in seen:
            lines.append(f'{prefix}{branch}{name}  (see above)')
            return
        seen.add(f)
        status = kurtc_status(f)
        certified = f', certificates {date(f + "c")}' if status.startswith('certified') else ''
        lines.append(f'{prefix}{branch}{name}  -- {status}  (file {date(f)}{certified})')
        children = loaded_files(f)
        inner = prefix + ('' if top else ('   ' if last else '│  '))
        for i, child in enumerate(children):
            show(child, inner, i == len(children) - 1, False)
    show(fname, '', True, True)
    return '\n'.join(lines)

def align(old: Expr, new: Expr, names: dict[str, str]) -> bool:
    # whether `new` is `old` with its canonical names (`$$c3`) replaced by names, consistently --
    # extends `names` by the replacements
    if isinstance(old, Token):
        if not isinstance(new, Token):
            return False
        if isinstance(old.value, str) and old.value[2:3] == 'c' and is_internal_name(old.value[:2] + old.value[3:]):
            if not (isinstance(new.value, str) and new.label == 'SYMBOL' and is_internal_name(new.value)):
                return False        # a canonical name stands for an internal variable, never a constant
            return names.setdefault(old.value, new.value) == new.value
        return old.label == new.label and old.value == new.value
    if not isinstance(new, list) or len(old) != len(new):
        return False
    return all(align(o, n, names) for o, n in zip(old, new))

def resolve_formula(j: dict, names: dict[str, str], kb: KnowledgeBase) -> Optional[Formula]:
    # the formula of the theory that `j` (see `formula_to_json`) describes, extending `names`
    stored = expr_from_json(j['expr'])
    for f in kb.all_theory():
        if f.filename != j['file'] or f.line != j['line'] or f.label != j['label']:
            continue
        found = dict(names)
        if not align(stored, f.simplified_expr, found):
            continue
        names.update(found)
        if j['direction'] is None:
            return f
        source = f.simplified_expr
        if not is_iff(source):
            return None             # only an `iff` has two directions
        assert isinstance(source, list) and len(source) == 3 and isinstance(source[0], Token)
        L, R = (source[1], source[2]) if j['direction'] == 'lr' else (source[2], source[1])
        clone = f.clone([source[0].clone(IMPL_SYMBOL), L, R], kb)
        clone.direction_of = source
        return clone
    return None

def rebuild_certificate(h: dict, names: dict[str, str], goal: Expr, fixed: frozenset[str], kb: KnowledgeBase) -> Optional[Certificate]:
    # a stored certificate (see `certificate_to_json`) for the goal and facts as they are now
    rule = resolve_formula(h['rule'], names, kb)
    if rule is None:
        return None
    facts = [resolve_formula(j, names, kb) for j in h['facts']]
    if any(f is None for f in facts):
        return None
    def name(c: str) -> str:
        # a canonical name: its name now, or a fresh one (for the fresh variables of `∀`s, and
        # for variables that only occur in values)
        if c not in names:
            names[c] = new_bool_var_name() if c.startswith('%') else new_var_name()
        return names[c]
    def rename(e: Expr) -> Expr:
        if isinstance(e, Token):
            if isinstance(e.value, str) and e.value[2:3] == 'c' and is_internal_name(e.value[:2] + e.value[3:]):
                return Token('SYMBOL', name(e.value))
            return e
        return [rename(c) for c in e]
    return Certificate('rule', goal, fixed, rule, h['form'], rule.simplified_expr,
                       tuple(name(c) for c in h['premise_fresh']), tuple(name(c) for c in h['conclusion_fresh']),
                       {name(c): rename(expr_from_json(v)) for c, v in h['values']},
                       [f for f in facts if f is not None], [tuple(name(c) for c in fresh) for fresh in h['fact_fresh']])

def replay_certificate(goal: Expr, fixed: frozenset[str], kb: KnowledgeBase) -> tuple[Optional[Certificate], bool]:
    # a stored certificate of the current line for `goal`, accepted by the kernel -- and whether
    # the line has stored certificates at all
    key = current_line[0]
    if key is None or key[0] not in replay_hints:
        return None, False
    hints = replay_hints[key[0]].get(key[1])
    if not hints:
        return None, False
    for i, h in enumerate(hints):
        try:
            names: dict[str, str] = {}
            if not align(expr_from_json(h['goal']), goal, names):
                continue
            cert = rebuild_certificate(h, names, goal, fixed, kb)
            if cert is None or kernel_verify(cert, kb) is not None:
                continue
        except Exception:       # a damaged `.kurtc`: only a hint that doesn't work
            continue
        del hints[i]
        certificates_by_line.setdefault(key, []).append((cert, None))
        return cert, True
    return None, True

############
## kernel ##
############
# Checks a certificate without any search: it strips the rule's outer `∀`s with the names the
# search used, fills in the values, evaluates `sub`, and compares the result with the goal and
# the facts. What it trusts besides its own code: the parser, `unpack_condition` (which variable
# a binder binds), `normalize_expr` (`flat`, `sym`, `calc`), and `equal_expr` (equality up to
# renaming bound variables).

class KernelReject(Exception):
    pass

def k_free(e: Expr, kb: KnowledgeBase, bound: frozenset[str] = frozenset()) -> set[str]:
    # the free variables of `e`
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str) and kb.is_var(v):
            return set() if v in bound else {v}
        case Token():
            return set()
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv, _ = unpack_condition(cond, kb)
            return set().union(*(k_free(c, kb, bound | {bv}) for c in [cond, *body]))
        case [*children]:
            return set().union(*(k_free(c, kb, bound) for c in children)) if children else set()
    raise KernelReject(f'unexpected expression `{e}`')

def k_rename(e: Expr, old: str, new: str) -> Expr:
    # rename the variable `old` to the fresh name `new`, everywhere (names are unique)
    if isinstance(e, Token):
        return Token('SYMBOL', new, e.column) if e.value == old else e
    return [k_rename(c, old, new) for c in e]

def k_dependencies(e: Expr, kb: KnowledgeBase) -> dict[str, str]:
    # which non-boolean schema variables may contain which bound variable: those that only occur
    # as the whole body of binders over the same variable, or as the body of `sub` for it (the
    # same criterion as `find_dependent_vars`, written again for the kernel)
    contexts: dict[str, list[Optional[tuple[str, bool]]]] = {}
    def note(t: Expr, context: Optional[tuple[str, bool]]) -> bool:
        if isinstance(t, Token) and isinstance(t.value, str) and t.value.startswith('$') and kb.is_var(t.value) and not kb.is_bool(t.value):
            contexts.setdefault(t.value, []).append(context)
            return True
        return False
    def walk(t: Expr) -> None:
        match t:
            case Token():
                note(t, None)
            case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x), a, A] if op == SUB_SYMBOL and isinstance(x, str):
                walk(a)
                if not note(A, (x, True)):
                    walk(A)
            case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
                bv, _ = unpack_condition(cond, kb)
                walk(cond)
                for c in body[:-1]:
                    walk(c)
                if body and not note(body[-1], (bv, False)):
                    walk(body[-1])
            case [*children]:
                for c in children:
                    walk(c)
    walk(e)
    result = {}
    for v, cs in contexts.items():
        binders = {c[0] for c in cs if c is not None}
        if None not in cs and len(binders) == 1 and any(not c[1] for c in cs if c is not None):
            result[v] = binders.pop()
    return result

def k_instantiate(e: Expr, values: dict[str, Expr], deps: dict[str, str], kb: KnowledgeBase, bound: frozenset[str] = frozenset()) -> Expr:
    # fill in the values of the variables -- without renaming, so a value may contain a variable
    # that is bound where the variable occurs only if that is meant: a boolean `%A` may (as in
    # "forall-elim"), a non-boolean `$T` only its own bound variable (see `k_dependencies`)
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
            bv, _ = unpack_condition(cond, kb)
            return [e[0], *(k_instantiate(c, values, deps, kb, bound | {bv}) for c in [cond, *body])]
        case [*children]:
            return [k_instantiate(c, values, deps, kb, bound) for c in children]
    raise KernelReject(f'unexpected expression `{e}`')

def k_replace(A: Expr, x: str, t: Expr, kb: KnowledgeBase) -> Expr:
    # `A` with `t` for the free occurrences of `x`, renaming a binder that would capture `t`
    match A:
        case Token(label='SYMBOL', value=v) if v == x:
            return deepcopy_expr(t)
        case Token():
            return A
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv, _ = unpack_condition(cond, kb)
            if bv == x:
                return A
            if bv in k_free(t, kb):
                fresh = new_bool_var_name(bv) if kb.is_bool(bv) else new_var_name(bv)
                A = k_rename(A, bv, fresh)
                assert isinstance(A, list)
            return [A[0], *(k_replace(c, x, t, kb) for c in A[1:])]
        case [*children]:
            return [k_replace(c, x, t, kb) for c in children]
    raise KernelReject(f'unexpected expression `{A}`')

def k_evaluate(e: Expr, kb: KnowledgeBase) -> Expr:
    # evaluate the `sub`s, innermost first; a `sub` with a still unknown `%A` stays
    match e:
        case Token():
            return e
        case [Token(label='SYMBOL', value=op), Token(label='SYMBOL', value=x) as tx, t, A] if op == SUB_SYMBOL and isinstance(x, str):
            t, A = k_evaluate(t, kb), k_evaluate(A, kb)
            if is_bool_var_token(A, kb) and A != tx:
                return [e[0], tx, t, A]
            return k_replace(A, x, t, kb)
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op) and is_sub(cond):
            # a binder with any condition, `∀ (sub $x $v C)`: `C` must not contain `$v` itself
            assert isinstance(cond, list)
            v = cond[2]
            assert isinstance(v, Token) and isinstance(v.value, str)
            if v.value in k_free(cond[3], kb):
                raise KernelReject(f'the condition `{expr_str(cond[3], kb)}` contains its bound variable `{v.value}`')
            return [e[0], *(k_evaluate(c, kb) for c in e[1:])]
        case [*children]:
            return [k_evaluate(c, kb) for c in children]
    raise KernelReject(f'unexpected expression `{e}`')

def k_instance(e: Expr, values: dict[str, Expr], deps: dict[str, str], kb: KnowledgeBase) -> Expr:
    return normalize_expr(k_evaluate(k_instantiate(e, values, deps, kb), kb), kb)

def k_strip(e: Expr, names: tuple[str, ...], also: Optional[Expr] = None) -> tuple[Expr, Optional[Expr]]:
    # remove outer `∀`s (without condition) of `e`, one per name, renaming the bound variable to
    # the name -- also in `also` (the conclusion, for the `∀`s of a premise)
    for name in names:
        match e:
            case [Token(label='SYMBOL', value=q), Token(label='SYMBOL', value=bv), body] if q == FORALL_SYMBOL and isinstance(bv, str):
                e = k_rename(body, bv, name)
                if also is not None:
                    also = k_rename(also, bv, name)
            case _:
                raise KernelReject(f'expected {len(names)} outer `{FORALL_SYMBOL}`s')
    return e, also

def k_known(f: Formula, kb: KnowledgeBase) -> bool:
    # whether `f` is a formula of the theory (or one direction of an `iff` of the theory)
    for g in kb.all_theory():
        if g is f:
            return True
        if f.direction_of is not None and g.id == f.id and g.simplified_expr is f.direction_of and is_iff(f.direction_of):
            L, R = f.direction_of[1], f.direction_of[2]      # type: ignore[index]
            e = f.simplified_expr
            return is_implication(e) and ((e[1] is L and e[2] is R) or (e[1] is R and e[2] is L))  # type: ignore[index]
    return False

def k_constants(e: Expr, kb: KnowledgeBase, bound: frozenset[str] = frozenset()) -> set[str]:
    # the symbols of `e` that are not variables and not bound
    match e:
        case Token(label='SYMBOL', value=v) if isinstance(v, str):
            return set() if v in bound or kb.is_var(v) else {v}
        case Token():
            return set()
        case [Token(label='SYMBOL', value=op), cond, *body] if isinstance(op, str) and kb.is_bindop(op):
            bv, _ = unpack_condition(cond, kb)
            return {op} | set().union(*(k_constants(c, kb, bound | {bv}) for c in [cond, *body]))
        case [*children]:
            return set().union(*(k_constants(c, kb, bound) for c in children)) if children else set()
    raise KernelReject(f'unexpected expression `{e}`')

def kernel_verify_block(cert: Certificate) -> Optional[str]:
    # closing a block: `cert.rule` is its last line, `cert.goal` the formula it gives
    block = cert.block
    assert block is not None and block.parent is not None and cert.rule is not None
    parent = block.parent
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
        # witness of a `pick` never, even if it is also a "vocabulary" symbol (`bool`, `arity`)
        leaked = {c for c in k_constants(e, parent) if c in block.const and not parent.is_var(c)
                  and (not block.is_vocabulary_symbol(c) or c == witness)}
        if leaked:
            return f'the constants {sorted(leaked)} of the block occur in `{expr_str(e, parent)}`'
        reading = binder_reading_changes(block, e, last.expr)
        return reading
    match cert.kind:
        case 'impl-intro' | 'not-intro':
            if block.mode_str not in ('assume', 'case') or len(block.mode_args) != 1:
                return 'not an `assume` or `case` block'
            assumption = block.mode_args[0]
            if cert.kind == 'impl-intro':
                expected: Expr = [Token('SYMBOL', IMPL_SYMBOL), assumption, last.expr]
            else:
                if not (isinstance(last.expr, Token) and last.expr.value == FALSE_SYMBOL):
                    return 'the last line is not `false`'
                expected = [Token('SYMBOL', NOT_SYMBOL), assumption]
            if not equal_expr(cert.goal, expected, parent, keep_order=False):
                return f'`{expr_str(cert.goal, parent)}` is not `{expr_str(expected, parent)}`'
            return no_escape(cert.goal)
        case 'forall-intro':
            if block.mode_str != 'let' or not block.mode_args:
                return 'not a `let` block'
            expected = last.expr
            for condition in reversed(block.mode_args):
                if is_bool_var_token(condition, parent):
                    continue
                v, _ = unpack_condition(condition, parent)
                if not new_in_block(v):
                    return f'`{v}` was not new in the `let` block'
                expected = [Token('SYMBOL', FORALL_SYMBOL), condition, expected]
            if not equal_expr(cert.goal, expected, parent, keep_order=False):
                return f'`{expr_str(cert.goal, parent)}` is not `{expr_str(expected, parent)}`'
            return no_escape(cert.goal)
        case 'exists-elim':
            if block.mode_str != 'pick' or len(block.mode_args) != 1 or block.pick_source is None or block.pick_fact is None:
                return 'not a `pick` block'
            witness = block.mode_args[0]
            if not (isinstance(witness, Token) and isinstance(witness.value, str) and new_in_block(witness.value)):
                return f'the witness `{expr_str(witness, parent)}` was not new in the `pick` block'
            if not k_known(block.pick_source, parent):
                return 'the existential fact is not in the theory'
            match block.pick_source.simplified_expr:
                case [Token(label='SYMBOL', value=q), Token(label='SYMBOL', value=x), body] if q == EXISTS_SYMBOL and isinstance(x, str):
                    instance = normalize_expr(k_replace(body, x, witness, parent), parent)
                case _:
                    return 'the fact picked from is not an existential'
            if not equal_expr(instance, normalize_expr(block.pick_fact.expr, parent), parent, keep_order=False):
                return f'the fact `{expr_str(block.pick_fact.expr, parent)}` about the witness is not `{expr_str(instance, parent)}`'
            if not equal_expr(cert.goal, last.expr, parent, keep_order=False):
                return 'the block does not give its last line'
            return no_escape(cert.goal)
    return f'unknown block rule `{cert.kind}`'

def kernel_verify(cert: Certificate, kb: KnowledgeBase) -> Optional[str]:
    # `None` if the certificate proves its goal, otherwise what is wrong
    try:
        if cert.block is not None:
            return kernel_verify_block(cert)
        goal = normalize_expr(cert.goal, kb)
        match cert.kind:
            case 'todo':
                return None                 # admitted, and reported as a `todo`
            case 'top':
                return None if isinstance(cert.goal, Token) and cert.goal.value == TRUE_SYMBOL else 'not `true`'
            case 'calc':
                return None if numeric_comparison_holds(cert.goal, kb) else 'the comparison does not hold'
            case 'calc-fact':
                assert cert.rule is not None
                if not k_known(cert.rule, kb):
                    return 'the fact is not in the theory'
                return None if equal_expr(calculate_normalized(cert.rule.expr, kb), calculate_normalized(cert.goal, kb), kb, keep_order=False) else 'the fact does not compute to the goal'
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
        deps = k_dependencies(cert.expr, kb)
        if cert.form == 'fact':
            if cert.premise_fresh or cert.conclusion_fresh or cert.facts:
                return 'a fact has no premise'
            instance = k_instance(cert.expr, cert.values, deps, kb)
            return None if equal_expr(instance, goal, kb, keep_order=False) else f'the instance `{expr_str(instance, kb)}` is not the goal'
        if cert.form != 'impl' or not is_implication(cert.expr):
            return f'unknown form `{cert.form}`'
        assert isinstance(cert.expr, list)
        premise, conclusion = k_strip(cert.expr[1], cert.premise_fresh, cert.expr[2])
        assert conclusion is not None
        conclusion, _ = k_strip(conclusion, cert.conclusion_fresh)
        # the fresh variables of the premise's `∀`s stand for anything: no value, and no variable
        # of the rule (except a boolean one, see `k_instantiate`) may depend on them
        eigen = set(cert.premise_fresh).union(*cert.fact_fresh)
        if eigen & set(cert.values):
            return f'the fresh variables {sorted(eigen & set(cert.values))} of a `∀` premise got a value'
        rule_vars = {t.value for t in get_token_set(cert.expr) if isinstance(t.value, str) and kb.is_var(t.value) and not kb.is_bool(t.value)}
        for v in rule_vars:
            if v in cert.values and k_free(cert.values[v], kb) & eigen:
                return f'the value of `{v}` depends on the fresh variables {sorted(k_free(cert.values[v], kb) & eigen)} of a `∀` premise'
        instance = k_instance(conclusion, cert.values, deps, kb)
        if not equal_expr(instance, goal, kb, keep_order=False):
            return f'the instance `{expr_str(instance, kb)}` of the conclusion is not the goal'
        facts = [k_instance(f.simplified_expr, cert.values, k_dependencies(f.simplified_expr, kb), kb) for f in cert.facts]
        def covered(part: Expr, strips: list[tuple[str, ...]]) -> bool:
            # `part` of the premise is an instance of a fact, or a `∀` whose body is (with one of
            # the recorded fresh variables), or a conjunction of such parts
            if any(equal_expr(part, fact, kb, keep_order=False) for fact in facts):
                return True
            if is_forall(part) and isinstance(part, list) and isinstance(part[1], Token):
                for i, names in enumerate(strips):
                    try:
                        body, _ = k_strip(part, names)
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
                        i = next((i for i, r in enumerate(remaining) if equal_expr(c, r, kb, keep_order=False)), None)
                        if i is None:
                            break
                        del remaining[i]
                    else:
                        if len(remaining) < len(parts) and not any(r is first for r in remaining) and covered_all(remaining, strips):
                            return True
            return False
        premise_instance = k_instance(premise, cert.values, deps, kb)
        if not covered(premise_instance, list(cert.fact_fresh)):
            return f'the premise `{expr_str(premise_instance, kb)}` does not follow from the facts'
        return None
    except KernelReject as e:
        return str(e)

def resolved_values(s: State) -> dict[str, Expr]:
    # the value of each variable with a value in `s`, with the values of the variables in it
    # filled in (ignoring blocked variables: the certificate gives the final values)
    def resolve(e: Expr, seen: frozenset[str]) -> Expr:
        match e:
            case Token(label='SYMBOL', value=v) if isinstance(v, str) and v in s.subst and v not in seen:
                return resolve(s.subst[v], seen | {v})
            case Token():
                return e
            case [*children]:
                return [resolve(c, seen) for c in children]
        assert False, f'BUG: did not match `{e}` in `resolved_values`'
    return {v: resolve(t, frozenset({v})) for v, t in s.subst.items()}

# unify a list of expression with the theory
def match_all_theory(exprs: list[Expr], s: State, kb: KnowledgeBase) -> tuple[bool, list[Formula], State, list[tuple[str, ...]]]:
    # returns: success, the facts that matched, the state, and the fresh names of the `forall`s
    # stripped from `exprs` (for the certificate, see `Certificate`)
    match exprs:

        # we unified all `exprs`, done!
        case []:
            return True, [], s, []
        
        # still at least one to go
        case [expr, *tail]:
            # iterate over all formulas of the theory
            blocked = frozenset()   # no blocked variables
            for candidate in kb.all_theory():
                # iterate over all possible substitutions that unify
                # basically, this is two-sided matching, aka unification

                #debug(f'trying to match `{expr_str(expr, kb)}` against candidate `{expr_str(candidate.simplified_expr, kb)}`')
                for s_cand in unify_exprs_with_patterns([(candidate.simplified_expr, expr)], s, kb):
                    # try to unify the rest of the expressions (the `tail`)
                    s_local = s_cand
                    tail_local = []
                    try:
                        for e in tail:
                            e_local, s_tail = trigger_sub(e, s_local, kb)
                            tail_local.append(e_local)
                    except BinderMisread:
                        continue
                    if not all(valid_bindop_conditions(e, kb) for e in tail_local):
                        continue    # see the same check in `impl_elim`
                    success, found_formulas, s_final, strips = match_all_theory(tail_local, s_local, kb)
                    if success:
                        #debug(f'`{expr_str(expr, kb)}` against `{expr_str(candidate.simplified_expr, kb)}` with substitution {s_final}`')
                        return True, [candidate, *found_formulas], s_final, strips   # match was found!  BINGO!
            # no match so far, however, a universally quantified `expr` (e.g. one half of a
            # conjunctive premise) matches the stored facts only without its outer `forall`s,
            # since those are removed from all facts -- with fresh variables that must stay
            # generic, exactly like for a quantified premise in `impl_elim`
            expr_walked = s.walk(expr)
            stripped, fresh_vars = remove_outer_forall_quantifiers(expr_walked, kb) if is_forall(expr_walked) else (expr_walked, ())
            if fresh_vars:
                s_stripped = s
                for fresh_v in fresh_vars:
                    s_stripped = s_stripped.block_eigen(fresh_v)
                success, found_formulas, s_final, strips = match_all_theory([stripped, *tail], s_stripped, kb)
                if success:
                    return True, found_formulas, s_final, [fresh_vars, *strips]
            # still no match, however, possibly `expr` is a conjunction that we can split into pieces
            match expr:
                # e.g., (A and B) implies C, then `expr = ['and', A, B]`
                case [Token(label='SYMBOL', value=v), *exprs] if v == AND_SYMBOL:
                    # the only place where we might call `match_all_theory` with a list longer than one
                    assert len(exprs) > 0
                    return match_all_theory(exprs + tail, s, kb)  # try to match the arguments of the conjunction
            # still no match, so we return `None` and an empty list
            return False, [], State.empty(), []  # could not find a match among the candidate `patterns`

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
def impl_elim(expr: Expr, expr_free_vars: frozenset[str], proven_formula: Formula, filename: str, mainstream: bool, s: State, kb: KnowledgeBase) -> tuple[Optional[Certificate], State]:

    #debug(f'impl_elim: trying to prove `{expr_str(expr, kb)}` using `{expr_str(proven_formula.expr, kb)}`')

    # continue with the renamed and simplified variant of `proven_formula` that is generated during the construction of it
    formula_expr: Expr = proven_formula.simplified_expr

    # assign `conclusion` and `premises`
    premise: Optional[Expr] = None
    premise_fresh_vars: tuple[str, ...] = ()
    conclusion_fresh_vars: tuple[str, ...] = ()
    strips: list[tuple[str, ...]] = []
    if is_implication(formula_expr):      # case 1: implication with a premise
        assert isinstance(formula_expr, list)
        premise, conclusion, premise_fresh_vars = strip_premise_with_synced_conclusion(formula_expr[1], formula_expr[2], kb)
        # the conclusion may *also* have its own outer forall(s), independent of the
        # premise's (e.g. "induction"'s premise is `and`-headed, but its conclusion is
        # `forall $n in Nat (...)`) -- strip those too. Safe to leave their fresh names
        # unblocked: they get resolved via ordinary unification against the real goal
        # (`expr`), not via a premise search, so the soundness issue this function's sibling
        # guards against doesn't apply here.
        conclusion, conclusion_fresh_vars = remove_outer_forall_quantifiers(conclusion, kb)
    elif is_iff(formula_expr):
        assert isinstance(formula_expr, list)
        op_token = formula_expr[0]
        assert isinstance(op_token, Token)
        # deliberately NOT stripped here (unlike the implication case above): stripping now
        # and discarding the resulting fresh-var set would lose exactly the information the
        # recursive `impl_elim` call below needs to block them correctly during its own
        # premise search -- passing the raw, unstripped LHS/RHS through defers stripping (and
        # fresh-var tracking) to that recursive call's own case-1 handling above, which does
        # this eigenvariable bookkeeping correctly. See doc/kurt-soundness.md's writeup of the
        # bug this matters for.
        LHS = formula_expr[1]
        RHS = formula_expr[2]
        # first attempt: LHS implies RHS
        LHSimpliesRHS = proven_formula.clone([op_token.clone(IMPL_SYMBOL), LHS, RHS], kb)
        LHSimpliesRHS.direction_of = formula_expr
        cert, s_local = impl_elim(expr, expr_free_vars, LHSimpliesRHS, filename, mainstream, s, kb)
        if cert is not None:
            return cert, s_local
        # second attempt: RHS implies LHS
        RHSimpliesLHS = proven_formula.clone([op_token.clone(IMPL_SYMBOL), RHS, LHS], kb)
        RHSimpliesLHS.direction_of = formula_expr
        cert, s_local = impl_elim(expr, expr_free_vars, RHSimpliesLHS, filename, mainstream, s, kb)
        if cert is not None:
            return cert, s_local
        # third attempt: LHS iff RHS directly -- block `expr`'s own free variables here too
        # (same reasoning as the case-1/2 blocking below, and the forall-elim fix, see
        # doc/kurt-soundness.md): without this, a goal like `a iff C` (`a` a free/schema
        # variable, `C` an unrelated fixed fact) unifies directly against e.g. `not-not`'s
        # `%A iff (not (not %A))` by binding `a`'s own fresh internal name straight to
        # `not (not C)` -- a genuinely free variable in the goal getting silently assigned a
        # concrete value that makes some unrelated axiom match, rather than the goal holding
        # for whatever `a` actually is. This third attempt is the *only* `is_iff` path that
        # unifies `expr` directly (attempts one/two recurse into the case-1/2 branch above,
        # which already blocks correctly) -- found via a `var`-declared symbol whose
        # auto-inferred boolean-ness was the original, narrower symptom reported.
        blocked_as_domain = frozenset(s.blocked_as_domain | expr_free_vars)
        s_blocked = State(s.subst, blocked_as_domain, s.blocked_as_range, s.eigen)
        s_final = _first_or_none(unify_exprs_with_patterns([(expr, formula_expr)], s_blocked, kb))
        if s_final is not None:
            cert = record_certificate(Certificate('rule', expr, expr_free_vars, proven_formula, 'fact', formula_expr, values=resolved_values(s_final)), kb)
            return cert, s_final
        return None, State.empty()    # no luck this time
    else:                                 # case 2: "implication" with an empty premise (think of `true implies $A`)
        conclusion = formula_expr

    # to unify `conclusion` and `premise` iterate over all possible substitutions of the `conclusion`
    # however, we must not change bound variables, so we block the free variables of `expr` since they are universally quantified
    blocked_as_domain = frozenset(s.blocked_as_domain | expr_free_vars)
    s = State(s.subst, blocked_as_domain, s.blocked_as_range, s.eigen)
    s_final: Optional[State] = State.empty()
    for s_matched in unify_exprs_with_patterns([(expr, conclusion)], s, kb):
        #f'impl_elim: matched `{expr}` with conclusion `{expr_str(conclusion, kb)}` with substitution {s_matched}')
        if premise is None:
            s_final = s_matched
            break           # bingo!  we found one
        else:
            # deep copy of `premise` is necessary, since `match_all_theory` will be called several times with the different substitution `subst`
            # and we have to apply the various substitutions to it, which might change from call to call
            try:
                premise_local, s_local = trigger_sub(premise, s_matched, kb)
            except BinderMisread:
                continue
            if not valid_bindop_conditions(premise_local, kb):
                continue        # e.g. `∀ (sub $x $v %C) %P` with a `%C` that doesn't mention `$x`

            # block the premise's own freshly-introduced eigenvariables (from stripping this
            # axiom's own antecedent forall, above) from being resolved to a specific value
            # during the search below -- they stand for a genuinely arbitrary/generic
            # instance ("true for all x"), not something the search gets to pick. Without
            # this, e.g. forall-elim's own premise `forall $x %A` degenerates (via a
            # legitimate single-hole decomposition of the *conclusion*, `%A := ($x = g)`)
            # into needing just `$$fresh = g` -- and unifying that fresh eigenvariable
            # straight to a concrete value like `g` let ANY two objects be proven equal, a
            # real soundness bug found and fixed this session (see doc/kurt-soundness.md).
            for fresh_v in premise_fresh_vars:
                s_local = s_local.block_eigen(fresh_v)

            # search for the premise as well, i.e., match the theory against the `premise`
            success, matched_formulas, s_final, strips = match_all_theory([premise_local], s_local, kb)
            if success:
                break           # bingo!  we found one
    else:
        if is_implication(formula_expr):
            # maybe we shouldn't split it into premise and conclusion
            premise = None
            s_final = _first_or_none(unify_exprs_with_patterns([(expr, formula_expr)], s, kb))
            if s_final is None:
                return None, State.empty()    # no luck this time
        else:
            return None, State.empty()     # no luck this time
    assert s_final is not None
    if premise is None:     # the goal is an instance of the formula
        cert = record_certificate(Certificate('rule', expr, expr_free_vars, proven_formula, 'fact', formula_expr, values=resolved_values(s_final)), kb)
    else:
        cert = record_certificate(Certificate('rule', expr, expr_free_vars, proven_formula, 'impl', formula_expr,
                                       premise_fresh_vars, conclusion_fresh_vars, resolved_values(s_final),
                                       list(matched_formulas), strips), kb)

    if kb.verbose:
        log(kb, '', f'  expression to prove: {expr_str(expr, kb)}', kb.level)
        log(kb, '', f'  formula used: {expr_str(proven_formula.expr, kb)}', kb.level)
    return cert, s_final    # bingo!  found an implication (and a substitution)

def get_column(e: Expr) -> int:
    match e:
        case Token():
            assert isinstance(e.column, int)
            return e.column
        case [*children] if len(children) > 0:
            return get_column(children[0])
    return 0

def calculate_normalized(expr: Expr, kb: KnowledgeBase) -> Expr:
    # compute all literal arithmetic in `expr` and bring the result into normal form again
    # (flattened before and after: `1 + (1 + k)` must become `2 + k`)
    return symmetrize_all(flatten_all(kb.calculate(flatten_all(expr, kb)), kb), kb)

def normalize_expr(expr: Expr, kb: KnowledgeBase) -> Expr:
    # the normal form of what the user types (see `post_process`): flat, sorted (`sym`), and,
    # with `calc on`, computed -- needed again for expressions created by substitution
    if kb.calc:
        return calculate_normalized(expr, kb)
    return symmetrize_all(flatten_all(expr, kb), kb)

def numeric_comparison_holds(expr: Expr, kb: 'KnowledgeBase') -> bool:
    # e.g. `3 <= 4` holds, while `2 = 3` and `x < 4` do not -- for a relation bound to the calculator
    match expr:
        case [Token(label='SYMBOL', value=op), a, b] if isinstance(op, str):
            va, vb = number_value(a, kb), number_value(b, kb)
            if va is None or vb is None:
                return False
            for relation in kb.get_calc_ops(op):
                if relation in CALCULATOR_RELATIONS:
                    return CALCULATOR_RELATIONS[relation](Fraction(va), Fraction(vb))
    return False

def derive_expr(expr: Expr, filename: str, mainstream: bool, s: State, kb: KnowledgeBase) -> tuple[list[Certificate], State]:
    # the certificates of the steps (one, or one per conjunct), see `Certificate.short` for the reasons

    # do we have a joker?  a bare `todo` right before admits the next step (only that one)
    if len(kb.theory) > 0:
        match kb.theory[-1].expr:
            case Token(label='TODO', value=''):
                return [record_certificate(Certificate('todo', expr, frozenset()), kb)], s

    # rename variables
    expr, _ = remove_outer_forall_quantifiers(expr, kb)
    expr = rename_all_vars(expr, kb)    # rename variables

    # "top-intro"
    if isinstance(expr, Token) and expr.label=='SYMBOL' and expr.value==TRUE_SYMBOL:
        return [record_certificate(Certificate('top', expr, frozenset()), kb)], s

    # "calc": with `calc on`, a comparison of two literal numbers is checked by computing it,
    # and a fact that computes to `expr` (e.g. `x = (-5) * 5` for `x = -25`) gives `expr`
    if kb.calc:
        if numeric_comparison_holds(expr, kb):
            return [record_certificate(Certificate('calc', expr, frozenset()), kb)], s
        calc_expr = calculate_normalized(expr, kb)
        for f in kb.all_theory():
            if equal_expr(calculate_normalized(f.expr, kb), calc_expr, kb):
                return [record_certificate(Certificate('calc-fact', expr, frozenset(), f), kb)], s

    # computed once here since `expr` is fixed for the whole loop below -- `impl_elim` used to
    # recompute this itself on every single formula tried (and again on every one of its own
    # recursive self-calls for an `is_iff` fact), turning an O(expr size) computation into
    # O(theory size * expr size) per derivation attempt for no reason, since the answer never
    # changes across the loop. See doc/kurt-soundness.md #6.
    expr_free_vars = free_bound_vars(expr, kb)[0]

    # a stored certificate for this goal (`.kurtc`), checked by the kernel, saves the search; if
    # the line has certificates, but none for this goal (e.g. for a conjunction proven clause by
    # clause), the search for it is only tried when nothing else works
    replayed, has_hints = replay_certificate(expr, expr_free_vars, kb)
    if replayed is not None:
        return [replayed], s

    def search() -> Optional[tuple[list[Certificate], State]]:
        # "impl-elim": iterate over the previously proven formulas that form the current theory.
        # this part also handles restatements (as implication without a premise)
        for proven_formula in kb.all_theory():
            cert, s_matched = impl_elim(expr, expr_free_vars, proven_formula, filename, mainstream, s, kb)
            if cert is not None:
                return [cert], s_matched
        return None

    if not has_hints:
        found = search()
        if found is not None:
            return found

    # if `expr` is a conjunction we can try to derive each of the subexpressions
    # make sure that, if it was a conjunction, then the (growing) substitution should apply to all clauses!
    match expr:
        case [Token(label='SYMBOL', value=v), *clauses] if v==AND_SYMBOL:
            reasons: list[Certificate] = []
            assert len(clauses) > 0
            s_clauses = s
            try:
                for clause in clauses:
                    more_reasons, s_clauses = derive_expr(clause, filename, mainstream, s_clauses, kb)  # this might raise an exception
                    reasons.extend(more_reasons)
                return reasons, s_clauses
            except KurtException:
                if not has_hints:
                    raise
                found = search()
                if found is None:
                    raise
                return found

    if has_hints:
        found = search()
        if found is not None:
            return found

    # couldn't derive formula using any of the rules
    raise KurtException(f'ProofError: can not derive `{expr_str(expr, kb)}`', column=get_column(expr))

LHS_value = '$$LHS$$'
LHS_token = Token('SYMBOL', value=LHS_value) # a special token to mark the LHS of the last row

# create a state object for the lexer
@dataclass
class LexerState:
    # for the chaining of infix operators across multiple lines
    initial_LHS: Optional[Expr] = None                           # LHS of the line starting the chain
    chained_ops: list[Token] = field(default_factory=list)       # infix operators of the chain seen so far
    # for the indentation handling
    indent_stack: list[int] = field(default_factory=lambda: [0]) # stack of indentation levels (in spaces)
    indent_requester: str = ''                                   # the keyword requesting an indented block
    # for good diagnostics
    line: int = 0                                                # current line number
    col: int = 0                                                 # current column number

def count_leading_spaces(s: str) -> int:
    # (tabs are already converted to spaces by `read_eval_loop`)
    return len(s) - len(s.lstrip())

def scan_parse_check_eval(input_line: str, lexer_state: LexerState, kb: KnowledgeBase, line: int, filename: str, mainstream:bool=False) -> tuple[KnowledgeBase, LexerState]:
    # the certificates of the steps of this line are kept for `cert` -- unless the line fails
    key = (filename, line)
    outer = current_line[0]
    current_line[0] = key
    certificates_by_line.pop(key, None)
    # the indentation and chain state before the line: a line that fails (or needs more input)
    # leaves it as it was -- unless it closed blocks before failing, then it matches those
    saved = LexerState(lexer_state.initial_LHS, list(lexer_state.chained_ops), list(lexer_state.indent_stack),
                       lexer_state.indent_requester, lexer_state.line, lexer_state.col)
    def restore() -> None:
        lexer_state.initial_LHS, lexer_state.chained_ops = saved.initial_LHS, saved.chained_ops
        lexer_state.indent_stack, lexer_state.indent_requester = saved.indent_stack, saved.indent_requester
    try:
        return scan_parse_check_eval_line(input_line, lexer_state, kb, line, filename, mainstream)
    except StopIteration:
        restore()
        raise
    except RecursionError:
        certificates_by_line.pop(key, None)
        restore()
        raise KurtException(f'EvalError: the expression is nested too deeply (Python\'s recursion limit) -- split it up, e.g. with `def`') from None
    except KurtException as e:
        certificates_by_line.pop(key, None)
        restore()
        indent = count_leading_spaces(input_line)
        if saved.indent_requester and indent > saved.indent_stack[-1]:
            # the failed line was the first of a block: the block is open, with this indentation
            lexer_state.indent_stack = saved.indent_stack + [indent]
            lexer_state.indent_requester = ''
        if e.kb_after is not None:
            # the blocks closed by the line stay closed, and so does their indentation (and a chain)
            del lexer_state.indent_stack[open_block_depth(e.kb_after) + 1:]
            lexer_state.initial_LHS, lexer_state.chained_ops, lexer_state.indent_requester = None, [], ''
        raise
    finally:
        current_line[0] = outer

def scan_parse_check_eval_line(input_line: str, lexer_state: LexerState, kb: KnowledgeBase, line: int, filename: str, mainstream:bool=False) -> tuple[KnowledgeBase, LexerState]:

    # read some lexer state variables for chaining
    lhs: Optional[Expr] = lexer_state.initial_LHS
    ops: list[Token] = lexer_state.chained_ops

    # count the indentation and strip leading spaces
    leading_spaces = count_leading_spaces(input_line)
    input_line = input_line.lstrip()   # remove leading spaces for parsing

    # scan the input line and prepare for the parsing
    ts = PeekableGenerator(scan_string(input_line, kb))    # runs the lexer

    # indentation handling before parsing
    # three cases:
    # 1. increased indentation, check that we expected it or that we are starting a chain
    # 2. same indentation, do nothing or continue chain
    # 3. decreased indentation, pop levels until we reach the new level or stop a chain
    requested = False       # was this indentation requested by a keyword opening a block?
    if leading_spaces > lexer_state.indent_stack[-1]:
        if len(lexer_state.indent_requester) > 0:
            requested = True
            lexer_state.indent_requester = ''       # reset expectation
        elif len(ops) == 1:
            # we are starting a chain, once allow increased indentation
            pass 
        else:
            raise KurtException(f'ParseError: unexpected increased indentation at line {line} in {filename}')
        # no error, so push the new indentation level
        lexer_state.indent_stack.append(leading_spaces)
        indents = 1   # a single indent, this is required for starting a chain
        dedents = 0   # the pushing of a new level is handled during evaluation (or we have a chain)
    else:
        # either case 2 or case 3
        if len(lexer_state.indent_requester) > 0:
            raise KurtException(f'ParseError: expected increased indentation at line {line} in {filename} after `{lexer_state.indent_requester}`.')
        # calculate number of DEDENTS
        indents = 0   # no new indent
        dedents = 0   # how many levels should we pop?
        assert len(lexer_state.indent_stack) > 0, 'BUG: indentation stack empty during decrease, should at least contain zero.'
        if len(ops) > 1 and leading_spaces < lexer_state.indent_stack[-1]:
            # reset the chain on dedent, that counts as closing one block
            lhs = None
            ops = []
            lexer_state.indent_stack.pop()
        while leading_spaces < lexer_state.indent_stack[-1]:
            lexer_state.indent_stack.pop()
            dedents += 1     # count the DEDENTs
            assert len(lexer_state.indent_stack) > 0, 'BUG: indentation stack empty during decrease, should at least contain zero.'
        if leading_spaces != lexer_state.indent_stack[-1]:
            raise KurtException(f'ParseError: new indentation at line {line} in {filename} does not match any previous block.')

    assert leading_spaces == lexer_state.indent_stack[-1], 'BUG: indentation level does not match the stack top after processing.'

    # chain management before parsing
    chained = False
    first_token: Optional[Token] = ts.peek # do we have a chainable operator at the start?
    if first_token is not None:
        first_label = first_token.label
        first_value = first_token.value
        if first_label == 'SYMBOL' and isinstance(first_value, str):
            if first_value not in keywords and kb.is_chainable(first_value):
                if lhs is not None and ops != []:         # did we start a chain before?
                    if len(ops) == 1  and  indents != 1:
                        raise KurtException(f'ParseError: expected indentation to start the chain at line {line} in {filename}')
                    if len(ops) > 1  and  (indents != 0 or dedents != 0):
                        raise KurtException(f'ParseError: unexpected indentation change in continued chain at line {line} in {filename}')
                    ops = ops + [first_token]             # add to the chain so far (a copy, see `scan_parse_check_eval`)
                    resulting_op: Optional[Token] = kb.get_chain_op(ops)
                    if resulting_op is not None:
                        chained = True
                        ts.prepend(LHS_token)             # add dummy token to the front
                    else:
                        raise KurtException(f'ParseError: invalid chain of operators `{ops}` at line {line} in {filename}')

    if not chained and len(ops) > 1 and indents == 0 and dedents == 0 and leading_spaces > 0 and lexer_state.indent_stack[-1] == leading_spaces \
            and len(lexer_state.indent_stack) > open_block_depth(kb) + 1:
        # the indentation is the chain's, not a block's: this line must continue the chain
        raise KurtException(f'ParseError: a line indented like the chain above must continue it (start with an operator), at line {line} in {filename}')

    if indents == 1 and not requested and not chained:
        # indented after a line that could start a chain, but not continuing it
        lexer_state.indent_stack.pop()
        raise KurtException(f'ParseError: unexpected increased indentation at line {line} in {filename}')

    # the usual parsing (raises exception if `chained=False` but `first_token` is chainable)
    kb_predecessor = kb
    for i in range(dedents):
        assert kb_predecessor.parent is not None, f'BUG: too many dedents at line {line} in {filename}'
        kb_predecessor = kb_predecessor.parent   # go to the predecessor for parsing
    keyword_token, expr_list, label, local = parse_tokenstream(ts, kb_predecessor)  # runs the parser
    keyword_value = '' if keyword_token is None else keyword_token.value
    if keyword_value not in ('use', 'def', 'parse') and any(contains_symbol(e, SUB_SYMBOL) for e in expr_list if not isinstance(e, Token) or e.label == 'SYMBOL'):
        # `sub` is for writing axiom schemas; in a claim it would only stand for its own result
        raise KurtException(f'EvalError: `{SUB_SYMBOL}` is only allowed in `use` and `def`, to write axiom schemas -- write the result of the substitution instead')
    if keyword_value in ('use', 'def'):
        for e in expr_list:
            check_sub_not_nested(e)
            check_condition_holes(e, kb_predecessor)

    # behavior for `break`, `qed`, and pure DEDENTs -- indentation drives block closing
    # identically whether reading a file or the interactive shell:
    #   DEDENTs close any block, possibly yielding a formula (or discarding, for `sandbox`)
    #   `qed` is an optional, explicit way to close a `proof` block -- it still needs a real
    #     dedent (like any other close) but additionally double-checks you meant a `proof`
    #   `break` discards the current block immediately, without any dedent -- the only way
    #     to close a `sandbox` other than dedenting past it
    #   - dedenting indicates how many levels to close
    keyword = '' if keyword_token is None else keyword_token.value
    if keyword in keywords_closing_blocks:
        if len(expr_list) > 0:
            raise KurtException(f'ParseError: `{keyword}` does not take any arguments')
    if keyword == 'break' and dedents > 0:
        raise KurtException(f'ParseError: `{keyword}` cannot create dedentation at line {line} in {filename}')
    if keyword == 'qed' and dedents == 0:
        raise KurtException(f'ParseError: `qed` must be used with dedentation at line {line} in {filename}')

    # chain management continued
    if chained:
        # case 1: continue chain
        assert isinstance(expr_list, list)
        if len(expr_list) != 1:
            raise KurtException(f'ParseError: expected exactly continued chain, not several comma-separated ones')
        if not (isinstance(expr_list[0], list) and len(expr_list[0]) == 3 and expr_list[0][1] == LHS_token):
            raise KurtException(f'ParseError: a line continuing a chain is one operator and its right-hand side, like `  < b` -- put anything more in parentheses: `  < (b = c)`')
        assert resulting_op is not None       # otherwise we wouldn't be in `chained` mode
        expr_list[0][0] = resulting_op        # replace the infix operator
        assert lhs is not None
        expr_list[0][1] = deepcopy_expr(lhs)  # replace the dummy token
    else:
        if len(expr_list) == 1 and kb.starts_a_chain(expr_list[0]) and keyword not in keywords_opening_blocks:
            # case 2: start new chain
            assert isinstance(expr_list[0], list)
            assert len(expr_list[0]) == 3
            e0, e1, _ = expr_list[0]
            assert isinstance(e0, Token) and isinstance(e0.value, str)
            lhs = e1     # store the LHS (which is after parsing the second token)
            ops = [e0]   # store the initial operator (which is after parsing the first token)
        else:
            # case 3: reset the chain
            lhs = None
            ops = []

    # process the block closings
    if keyword == 'break':
        if kb.is_load_boundary:
            raise KurtException(f'EvalError: `break` has no block to close here -- this is the top level of the file, not a `sandbox` you opened yourself', keyword_token.column if keyword_token is not None else None)
        was_proof = kb.mode_str == 'proof'
        kb = kb.pop_level()             # just pop one level, discarding it, no proof step
        lexer_state.indent_stack.pop()  # pop one indentation level
        if was_proof:
            # abandon the `show` promise too, not just the `proof` attempt -- otherwise it's
            # still pending on the parent level and merging/closing that level later fails
            assert len(kb.show) > 0, f'BUG: breaking a `proof` block with no pending `show` on its parent'
            kb.show.pop()
        if mainstream:
            log(kb, 'break', f'{line} discarded the last block', kb.level)
    elif keyword == 'qed':
        # dry run to check the block modes and that we are not closing too many levels
        dedents_check = dedents
        kb_check: KnowledgeBase = kb
        while dedents_check > 0:   # the last one is checked after the loop
            mode_str = kb_check.mode_str
            if mode_str == 'sandbox':
                raise KurtException(f'EvalError: `qed` never closes a `sandbox`')
            elif mode_str == 'root':
                assert False, f'BUG: `qed` closed too many levels at line {line} in {filename}'
            elif dedents_check == 1 and mode_str != 'proof':
                raise KurtException(f'EvalError: `qed` must close a `proof` block at line {line} in {filename}, not a `{mode_str}` block')
            assert kb_check.parent is not None, f'BUG: `qed` closed too many levels'
            kb_check = kb_check.parent   # don't pop yet, just check
            dedents_check -= 1
        # now actually pop the levels
        try:
            while dedents > 0:
                if kb.mode_str == 'proof':
                    with users_comment(input_line if dedents == 1 else ''):
                        kb = eval_qed(kb, filename, line, mainstream)   # qed with a block, yield a formula
                else:
                    kb = eval_done(kb, filename, line, mainstream)  # done with a block, yield a formula (or an `expect`'s check)
                dedents -= 1
        except KurtException as e:
            e.kb_after = e.kb_after or kb
            raise
    else:
        # process the DEDENTs -- this is how every block ordinarily closes, `proof` included
        # (`eval_done` itself dispatches to `eval_qed` for a `proof`-mode level)
        try:
            while dedents > 0:
                kb = eval_done(kb, filename, line, mainstream)   # closes one level: yields a formula, or discards (for `sandbox`)
                dedents -= 1
        except KurtException as e:
            e.kb_after = e.kb_after or kb    # the blocks closed so far are closed (see `read_eval_loop`)
            raise

        # evaluate the expression
        new_symbols.clear()
        with users_comment(input_line):
            kb = eval_expression(keyword_token, expr_list, input_line, label, kb, line, filename, mainstream, local) # evaluation
        if len(new_symbols) > 0:
            names = ', '.join(f'`{n}`' for n in new_symbols)
            if strict_mode and not is_trusted_file(filename):
                raise KurtException(f'EvalError: {names} not declared -- with `--strict`, every symbol must be declared before its use (`const`, `var`, `bool`, ...)')
            if mainstream:
                log(kb, f'; new constant{"s" if len(new_symbols) > 1 else ""} {names}, not declared before', '', kb.level)
            new_symbols.clear()

    # update lexer state for indentation handling
    if keyword_token is not None and keyword_token.value in keywords_opening_blocks:
        lexer_state.indent_requester = keyword_token.value  # next line should be indented
    else:
        lexer_state.indent_requester = ''

    # update lexer state for chaining
    lexer_state.initial_LHS = lhs
    lexer_state.chained_ops = ops

    return kb, lexer_state

# recursion guard for `load`: absolute paths of files whose `load_file` call is currently
# in progress (i.e. somewhere further down the current call stack), so that a genuine cycle
# (`a.kurt` loads `b.kurt` loads `a.kurt`) raises a clean `KurtException` instead of recursing
# until Python's stack blows up with an uncaught `RecursionError`. A file is only added once
# we're about to actually read it, and always removed again in a `finally`, whether loading it
# succeeded, failed to parse/check, or wasn't found at this particular search path.
_loading_in_progress: set[str] = set()

def is_already_loaded(filename: str, kb: KnowledgeBase, search_paths) -> bool:
    # whether `load_file` would skip `filename`, since it finds it loaded before finding it anywhere else
    if not filename.endswith('.kurt'):
        filename += '.kurt'
    for path in search_paths:
        candidate = path / filename
        if kb.get_load_level(str(candidate)) is not None:
            return True
        if candidate.is_file():
            return False
    return False

# the exports of the files checked so far in this run (not the main file, which prints its
# steps): a file is checked once, not again for each file that loads it -- as long as it and the
# files it loads didn't change, and neither did the settings that decide what is accepted
_checked_exports: dict[tuple, tuple[ExportBundle, list[tuple[str, Optional[str]]]]] = {}

def checked_exports(fname: str, f: TextIO, candidate, loader: KnowledgeBase, mainstream: bool) -> ExportBundle:
    # check the file in a fresh context -- the core, and the files it loads itself, nothing of
    # its loader (whose facts it could otherwise use without loading them, and whose load order
    # would matter) -- and return what it exports
    key = (fname, source_hash(fname), strict_mode, tuple(str(p) for p in trusted_paths), kurtc_enabled)
    cached = _checked_exports.get(key) if not mainstream and key[1] is not None else None
    if cached is not None and all(source_hash(dep) == digest for dep, digest in cached[1]):
        return copy.deepcopy(cached[0])
    load_dependencies[fname] = []
    if kurtc_enabled:
        read_kurtc(fname)
    root = copy.deepcopy(core_kb)
    root.format, root.verbose, root.hint = loader.format, loader.verbose, loader.hint   # only how it looks
    kb = root.push_level('sandbox', [])    # (the level of the file)
    kb.tmp = True
    kb.is_load_boundary = True             # `break` must not be able to close this implicit level
    kb = read_eval_loop(f, kb, mainstream=mainstream)
    if kb.level > 1:
        raise KurtException(f'\nEvalError: inside `{fname}` not all blocks closed.')
    assert kb.level == 1, f'BUG: `load_file` decreased the level from 1 to {kb.level}'
    if is_trusted_file(fname):
        kb.frozen |= kb.declared_symbols()   # only this theory may change their meaning
    if kurtc_enabled and len(root.todos()) == 0 and isinstance(candidate, Path):
        write_kurtc(fname)       # checked completely: its certificates
    if len(kb.show) > 0:
        raise KurtException(f'EvalError: cannot merge and pop a level with promised formulas, got {len(kb.show)} formulas.')
    bundle = compute_exports(kb)
    validate_exports(bundle, kb, root, fname)
    bundle.todos = list(root.todos())
    if not mainstream and key[1] is not None:
        _checked_exports[key] = (copy.deepcopy(bundle), [(dep, source_hash(dep)) for dep in bundle.libs])
    return bundle

def symbol_declarations(kb: 'KnowledgeBase | ExportBundle', s: str) -> tuple:
    # how `s` is read: everything a `load` must not change about a symbol that both sides know
    if isinstance(kb, ExportBundle):
        return (kb.infix.get(s), kb.prefix.get(s), kb.postfix.get(s), kb.arity.get(s, 0), tuple(kb.bool.get(s, [])),
                s in kb.bindop, s in kb.flat, s in kb.sym, kb.alias.get(s), tuple(kb.calc_ops.get(s, [])), kb.brackets.get(s))
    return (kb.get_infix(s), kb.get_prefix(s), kb.get_postfix(s), kb.get_arity(s), tuple(kb.bool_sig(s)),
            kb.is_bindop(s), kb.is_flat(s), kb.is_sym(s), kb.get_alias(s), tuple(kb.get_calc_ops(s)), kb.get_lbracket(s))

def validate_against_loader(bundle: ExportBundle, loader: 'KnowledgeBase', fname: str) -> None:
    # the file was checked on its own: a symbol it shares with its loader must mean the same on
    # both sides -- the same declarations, and, if it is defined, the same `def` (a `def` is only
    # conservative for a symbol that is new)
    clash = sorted(sym for sym in bundle.symbols if sym in bundle.const and loader.is_var(sym) and sym[0] not in '$%')
    if clash:
        raise KurtException(f'EvalError: {", ".join(f"`{c}`" for c in clash)} is a constant of the loaded file, but a variable here -- load the file before `var`, or rename the variable')
    def key(f: 'Formula') -> tuple[str, str, str]:
        return (f.filename, f.line, f.label)
    loader_formulas = [f for node in loader.levels() for f in node.theory]
    loader_defs = {f.def_symbol: key(f) for f in loader_formulas if f.def_symbol is not None}
    bundle_defs = {f.def_symbol: key(f) for f in bundle.theory if f.def_symbol is not None}
    core = core_kb.declared_symbols() | core_kb.used
    for sym in sorted(bundle.symbols - core):
        if sym[0] in '$%' or not loader.is_known(sym):
            continue
        # a later file may add to a symbol (arith.kurt binds `=` of equality.kurt to the
        # calculator), so a declaration may be missing on one side -- but not be another one
        if any(a and b and a != b for a, b in zip(symbol_declarations(loader, sym), symbol_declarations(bundle, sym))):
            raise KurtException(f'EvalError: `{sym}` is declared differently here and in `{fname}` -- rename it in one of them')
        if loader_defs.get(sym) != bundle_defs.get(sym):
            where = bundle_defs.get(sym) or loader_defs.get(sym)
            assert where is not None
            raise KurtException(f'EvalError: `{sym}` is defined in `{where[0]}` (line {where[1]}), but is another `{sym}` on the other side of `load {fname}` -- rename it in one of them')

def load_file(filename: str, kb: KnowledgeBase, search_paths = theory_path, mainstream:bool=False, silent:bool=False) -> KnowledgeBase:
    # files are always loaded into a new level that is dropped once everything is ok to avoid partial loads
    if not filename.endswith('.kurt'):
        filename += '.kurt'
    # a packaged theory is always loaded from the package, and must not be shadowed
    packaged = packaged_theory_file(filename)
    if packaged is not None:
        for path in search_paths:
            shadow = path / filename
            if is_packaged_path(path) or str(shadow) == str(packaged):
                break
            if shadow.is_file():
                raise KurtException(f'EvalError: `{shadow}` has the same name as the theory `{filename}` that comes with Kurt, and would shadow it -- please rename your file')
        search_paths = packaged_theory_paths
    # iterate over all theory paths
    for path in search_paths:
        candidate = path / filename
        fname = str(candidate)
        # check if the file was loaded already
        load_level = kb.get_load_level(fname)
        if load_level is not None:
            if current_line[0] is not None:
                load_dependencies.setdefault(current_line[0][0], []).append(fname)
            if kb.verbose:
                log(kb, f'; file `{fname}` has already been loaded, skipping.')
            return kb

        # is this exact file already being loaded further down the call stack? that's a cycle
        if fname in _loading_in_progress:
            raise KurtException(f'EvalError: circular `load`: `{fname}` is already being loaded (load cycle)') from None

        # try to open the file at this candidate path -- only *this* step's failure means
        # "not here, try the next search path"; anything raised while evaluating its contents
        # (below) is a real error and must propagate, not get silently reinterpreted as
        # "file not found" (that previously masked a genuine `AttributeError` bug elsewhere,
        # e.g. `read_eval_loop` needing an input stream's `.name`, as a confusing "unable to
        # open" message pointing at every search path instead of the real exception)
        try:
            candidate_file = candidate.open(encoding='utf-8')
        except (FileNotFoundError, NotADirectoryError, AttributeError):
            continue    # try next path

        if current_line[0] is not None:
            load_dependencies.setdefault(current_line[0][0], []).append(fname)
        try:
            _loading_in_progress.add(fname)
            with candidate_file as f:
                bundle = checked_exports(fname, f, candidate, kb, mainstream)
            validate_against_loader(bundle, kb, fname)
            apply_exports(kb, bundle)
            for todo in bundle.todos:
                kb.todo_add(todo)
            kb.libs.append(fname)
            return kb
        except KurtException as e:
            e.kb_after = None       # a level of the loaded file's own context, not of the loader
            raise

        finally:
            _loading_in_progress.discard(fname)

    # we couldn't open the file anywhere
    if not silent:
        # we have to add `from None` to avoid exception chaining, since we only want to see the KurtException
        raise KurtException(f'EvalError: unable to open `{filename}` searching at {[str(p) for p in search_paths]}') from None
    return kb

###########################
## commandline interface ##
###########################

def kurt_prompt(level: int, line: int, continued: bool=False) -> str:
    p: str = ''
    p += level*'    '            # current level, just a visual hint -- not injected into what you type
    p += ';'                                   # commenting out (for copy and paste back into a file)
    p += '... ' if continued else f'[{line}] ' # continuation?
    return p

def enclosing_expect(kb: KnowledgeBase) -> Optional[KnowledgeBase]:
    # the innermost `expect` block around the current level (inside the current file)
    node: Optional[KnowledgeBase] = kb
    while node is not None and not node.is_load_boundary:
        if node.mode_str == 'expect':
            return node
        node = node.parent
    return None

def open_block_depth(kb: KnowledgeBase) -> int:
    # the number of blocks open in the current file, i.e., the index of the current block's
    # indentation in `LexerState.indent_stack`
    depth = 0
    node: Optional[KnowledgeBase] = kb
    while node is not None and not node.is_load_boundary and node.mode_str != 'root':
        depth += 1
        node = node.parent
    return depth

def read_eval_loop(input_stream: TextIO, kb: KnowledgeBase, mainstream: bool=False) -> KnowledgeBase:
    is_file   = (input_stream.name != '<stdin>')   # for non files we have a fancy prompt and we don't stop if an KurtException comes
    line       = 1
    continued  = False
    lexer_state = LexerState()   # lexer state for indentation management
    input_line = ''
    skip_deeper_than: Optional[int] = None   # skip the rest of an `expect` block after its error
    accepted_lines[input_stream.name] = []   # the accepted lines, for `save`
    pending: list[str] = []                  # the lines of the statement being read
    replay: Optional[str] = None             # a line to evaluate again (after an `expect` closed)
    if not is_file and readline:
        readline.parse_and_bind("tab: complete")    # enable tab completion
    while True:
        try:
            if replay is not None:
                new_line, replay = replay, None
            elif not is_file:
                # indentation is significant here exactly like in a file (see `scan_parse_check_eval`):
                # type or paste real leading spaces yourself to open/continue/close a block by
                # dedenting, the same way you would in a file. `qed`/`break` remain as explicit,
                # position-independent ways to close a block without relying on that.
                prompt_text = kurt_prompt(kb.level, line, continued)
                new_line = input(prompt_text).rstrip()     # read from stdin, leading spaces preserved
                new_line = replace_latex_syntax(new_line)  # automatic replacements in the shell before running the scanner
            else:
                # here indentation matters, we read exactly what is in the file
                new_line = input_stream.readline()
                if not new_line:
                    if continued:
                        # still mid-parse (e.g. an unclosed bracket) when the file ran out --
                        # raise instead of silently breaking, otherwise this looks exactly
                        # like a clean "Proof checked" even though everything from here on
                        # (including whatever the file's actual last statement should have
                        # been) was never read at all
                        raise KurtException(
                            f'ParseError: unexpected end of file while still parsing a statement that started around line {line} in {input_stream.name} -- unclosed bracket or incomplete expression?',
                            line=line, filename=input_stream.name)
                    break
                new_line = new_line.rstrip()
                if line == 1:
                    new_line = new_line.removeprefix('\ufeff')   # a byte order mark, invisible in editors
            new_line = new_line.expandtabs(tab_indent)     # tabs are ok, but are converted
            if not continued and (new_line.strip() == '' or new_line.lstrip().startswith(';')):
                # a blank line (or a line with only a comment) never carries anything to parse -- skip it outright rather
                # than feeding it through the indentation logic below, where its own leading-
                # space count (0, whether truly empty or just whitespace) would otherwise be
                # read as "dedent all the way back to column 0", incorrectly closing every
                # currently open block regardless of how deeply nested we actually are (e.g.
                # a blank line for readability inside a `proof`/`assume` block). Only skipped
                # when not `continued`, i.e. not already mid-statement (an unclosed bracket
                # spanning a blank line is still part of that statement, not a new one).
                accepted_lines[input_stream.name].append(new_line)
                line += 1
                continue
            if not continued and skip_deeper_than is not None:
                if count_leading_spaces(new_line) > skip_deeper_than:
                    line += 1
                    continue      # still inside the `expect` block whose error was confirmed
                skip_deeper_than = None
            input_line += new_line
            pending.append(new_line)
            try:
                kb, lexer_state = scan_parse_check_eval(input_line, lexer_state, kb, line, input_stream.name, mainstream)
                accept_statement(input_stream.name, pending)
                pending = []
            except StopIteration:  # while parsing: need more input, i.e., `kb` has not changed yet, `lexer_state` has not changed either
                input_line += ' '  # add a space to the input line
                continued = True
                line += 1
                continue
            except KurtException as e:
                if e.kb_after is not None:
                    kb = e.kb_after          # the blocks closed by the line before its error stay closed
                expect_kb = enclosing_expect(kb)
                if expect_kb is not None:
                    assert len(expect_kb.mode_args) == 1 and isinstance(expect_kb.mode_args[0], Token)
                    expected_kind = expect_kb.mode_args[0].value
                    if e.kind == expected_kind:
                        # confirmed: the block did exactly what it promised -- discard it with
                        # everything inside it (like `break` would), wherever inside it the
                        # error came from: a statement directly inside it, a nested block, or a
                        # nested block that failed to close
                        while kb is not expect_kb:
                            assert kb.parent is not None
                            kb.show.clear()     # discarded, so are its pending `show`s
                            kb = kb.pop_level()
                        kb.show.clear()
                        kb = kb.pop_level()
                        depth = open_block_depth(kb)
                        expect_indent = lexer_state.indent_stack[depth]
                        del lexer_state.indent_stack[depth + 1:]
                        lexer_state.indent_requester = ''
                        lexer_state.initial_LHS = None
                        lexer_state.chained_ops = []
                        if mainstream:
                            log(kb, f'expect "{expected_kind}"', f'{line} confirmed', kb.level)
                        if count_leading_spaces(input_line) > expect_indent:
                            accept_statement(input_stream.name, pending)   # part of the confirmed block
                            pending = []
                            skip_deeper_than = expect_indent    # skip the rest of the block
                            input_line = ''
                            continued = False
                            line += 1
                        else:
                            # the line is already outside the block, it only failed while closing
                            # the blocks inside it -- so it still has to be evaluated
                            # (again through the loop, so that its own errors are handled as usual)
                            input_line = ''
                            continued = False
                            accept_statement(input_stream.name, pending[:-1])
                            pending = []
                            replay = new_line
                        continue
                    elif not e.msg.lstrip().startswith('ExpectationError'):
                        e.msg = f'expect "{expected_kind}" expected a `{expected_kind}`, got a different error instead:\n{e.msg}'
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
                    pending = []                   # the statement is not saved
            input_line = ''  # Reset input
            continued = False
            line += 1
        except EOFError:
            log(kb, "\nBye!")      # this only happens when Ctrl-d is pressed in the interactive session
            break
    return kb

def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=f'a simple proof assistant ({made_by})')
    parser.add_argument("filename", nargs='?',                       help=f'check the proof in the file, w/o filename start interactively')
    parser.add_argument('-i', '--interactive',  action='store_true', help=f'enter read-eval-print loop after loading `filename`')
    parser.add_argument('-r', '--comment-indent', type=int, default=comment_indent, help=f'specify the indentation for comments (default: {comment_indent})')
    parser.add_argument('-s', '--strict',       action='store_true', help=f'for grading: reject `use`, `todo` and `chain` outside the theories that come with Kurt or are found via `-p`')
    parser.add_argument('-p', '--path',                              help=f'specify the path where `load` looks for theories after checking {theory_path}')
    parser.add_argument('-v', '--verbose',      action='store_true', help=f'show extra information during proof checking')
    parser.add_argument('-d', '--debug',        action='store_true', help=f'show debugging information')
    parser.add_argument('--no-kurtc',           action='store_true', help=f'neither write nor use `.kurtc` files (the certificates of a checked file, see doc/kurt-doc.md)')
    parser.add_argument('--deps',               action='store_true', help=f'show the files that `filename` loads, with the state of their certificates, without checking anything')
    return parser.parse_args()

def main() -> None:

    # a lot of the internal soundness checking in this file (occurs-checks, bound-variable
    # safety, block-closing invariants, ...) is written as plain Python `assert`s rather than
    # `raise KurtException`, since they are meant to be "can't happen" invariants rather than
    # user-facing errors. `python -O`/`-OO` strip all `assert` statements at compile time,
    # which would silently disable those checks -- refuse to run rather than risk accepting
    # an unsound proof that a debug build would have caught.
    if not __debug__:
        print('KurtException: refusing to run under `python -O`/`-OO` -- this would silently '
              'disable internal soundness checks written as `assert`, see `main()` in kurt.py',
              file=sys.stderr)
        sys.exit(1)

    # get the commandline args
    args = parse_args()

    # the knowledge base we start with on level 0
    kb = initial_kb

    # debug flag?
    global debug_flag
    debug_flag = args.debug

    # set reason indentation
    global comment_indent
    comment_indent = args.comment_indent

    # only the files and their certificates?
    if args.deps:
        if args.filename is None:
            sys.exit('--deps needs a file')
        fname = args.filename if args.filename.endswith('.kurt') else args.filename + '.kurt'
        if not os.path.isfile(fname):
            sys.exit(f'no file `{fname}`')
        print(dependencies_str(fname))
        sys.exit(0)

    # say hello
    log(kb, f'This is Kurt, v{version} ({made_by}), file {file_fingerprint()}')

    # readline history
    if readline:
        readline_history_file = os.path.expanduser('~/.kurt_history')         # should work on all platforms
        if os.path.exists(readline_history_file):
            try:
                readline.read_history_file(readline_history_file)                 # restore history
            except OSError:
                # e.g. a file with only the header is not readable (`rm ~/.kurt_history`, then
                # start `kurt` and quit it immediately with Ctrl-D, then start it again)
                pass
        def write_history() -> None:
            try:
                readline.write_history_file(readline_history_file)
            except OSError:
                pass            # no history then, but no traceback at exit
        atexit.register(write_history)   # register for automatic saving

    # verbosity?
    kb.verbose = args.verbose

    # theory path
    global theory_path
    if args.path is not None:
        theory_path.insert(1, Path(args.path))                    # user specified path
        trusted_paths.append(Path(args.path))

    # strict mode, for grading
    global strict_mode
    strict_mode = args.strict

    # `.kurtc` files: safe also with `--strict`, since the kernel checks each stored certificate
    global kurtc_enabled
    kurtc_enabled = not args.no_kurtc

    if kb.verbose:
        log(kb, f'Using theory path: {theory_path}')

    had_error = False
    try:
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
                    log(kb, f'Proof checked')
                elif n_todos == 1:
                    log(kb, f'Proof almost checked: {n_todos} todo.')
                else:
                    log(kb, f'Proof almost checked: {n_todos} todos.')
                for todo in todos:
                    log(kb, f'  {todo}')
        else:
            args.interactive = True

    except KurtException as e:
        print(e.msg, file=sys.stderr)
        had_error = True

    # read-eval-print loop with exception handling
    if args.interactive:
        kb = read_eval_loop(sys.stdin, kb, mainstream=True)

    # a caught KurtException while checking `args.filename` (e.g. a failed proof, a parse
    # error) must be visible in the exit code -- otherwise a script (CI, an autograder)
    # cannot tell a failed check from a successful one without scraping stderr text.
    # Errors during an interactive REPL session don't affect this, same as a Python REPL
    # exiting 0 regardless of exceptions raised while typing at it.
    exit(1 if had_error else 0)

if __name__ == '__main__':
    main()
