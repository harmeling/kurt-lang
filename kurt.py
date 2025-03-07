#!/usr/bin/env python3

## kurt.py
# the kurt programming language for proof writing and checking
# developed by Stefan Harmeling (2016-2025)

# config
version        = 0.1
made_by        = 'made by Stefan Harmeling, 2025'
md_indent      = 7                     # ignore all lines not starting with `md_indent` many spaces
proof_indent   = 4                     # how much to indent for a `proof` block
theory_path    = ['.', 'theories']     # default path for theories
default_theory = 'theory.kurt'         # default theory

## processing a kurt-file does the following steps in a single pass
# level1: lexing
# level2: parsing
# level3: proving

### NEXT
# TODO load always uses '.' and then 'theories', define a path variable and a function that finds the file
# TODO add filename in front of the line numbers
# TODO check whether everything promised has been proven
# TODO create constants automatically
# TODO rewrite expr_str using match
# TODO create nice outputs <file.kurt:128>
# TODO any checks required for 'bindop'?
# TODO next: implement `equal_elim`
# TODO next: implement first order inference, WE ARE IGNORING FOR NOW WHETHER VARIABLES ARE BOUND OR FREE
# TODO add `//` to the language
# TODO runtime; currently: `derive_expr` is O(n^k) where n is the length of the theory and k is the maximum number of premises of an proved implication, 
#      this could be speed up with better data structure to store the formulas of the theory, but let's first keep it slow, but understandable
# TODO Q: is the match of `match_expr` always unique?  we are assuming it!
# TODO turn `load_file` into a method of class KnowledgeBase
# TODO allow outer forall block around implications
# TODO put everything into a symbol table?  let's have it additionally.
# TODO right now 'parse 17 42 244' is allowed, even though '17' does not have arity 2.  this should lead to an error.
# TODO however, `parse (+) 18 42` works, but it shouldn't!  make it work by defining the arity of infix operators explicit to 2
# TODO write kurt integration for vscode, highlight the lines that are proven, https://microsoft.github.io/language-server-protocol/
# TODO two algorithms: constraint based (https://www.youtube.com/watch?v=H7x4THVU4BQ) and substitution based (W)
# TODO redo something like https://terrytao.wordpress.com/2023/12/05/a-slightly-longer-lean-4-proof-tour/
#                          https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/
# TODO organize the rules as a dictionary of lists with the top-level operator as the key
# TODO write more test code, also for the proof stuff
# TODO implement 'nonassoc', this could then be checked in 'post_process'
### LATER/MAYBE
# TODO LBYL and EAFP Coding Style? <https://realpython.com/python-lbyl-vs-eafp/>
# TODO use more 'match' statements?  E.g. in eval? <https://peps.python.org/pep-0636/>
# TODO implement comments as labels, i.e. store them in the formula and use them
# TODO introduce witness of a formula?
# TODO optionally give an output filename for the proof structure
# TODO do multi-line equations, and indentation for begin/end block
# TODO https://en.wikibooks.org/wiki/Haskell/Indentation#:~:text=The%20golden%20rule%20of%20indentation&text=When%20you%20start%20the%20expression,acceptable%20and%20may%20be%20clearer).&text=This%20tends%20to%20trip%20up,expressions%20must%20be%20exactly%20aligned.
# TODO maybe not: do automatic line continuation if more tokens are required, e.g. after '+'
# TODO format "latex", also allow custom latex formats
# TODO possibly 'a b' is problematic if there are no arities for 'a' defined?
# TODO keep the code below 1000 lines of code!  unlikely...
# TODO maybe yes: allow `(+)` to turn an infix operators into a function call with arity 2, similar prefix, postfix
# TODO replace functool.cmp_to_key

## all external libraries (let's keep the dependencies minimal)
import sys          # sys.stdin, sys.stderr
import os           # os.path.isfile
import argparse     # argparse.ArgumentParser
import re           # re.compile, re.VERBOSE, re.MULTILINE
import functools    # functools.cmp_to_key
import readline     # readline.parse_and_bind, readline.add_history

class KurtException(Exception):
    def __init__(self, msg, column=None):
        self.msg    = msg
        self.column = column

## the syntax is stored in a hierarchical knowledge base called `KnowledgeBase`
format_options = ['sexpr', 'normal']            # sexpr: (+ 1 (* 3 4)), normal: (1 + (3 * 4))
keywords = {
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

    # syntactic sugar
    'theorem':     'plan to prove a formula and flag it "theorem"',
    'lemma':       'plan to prove a formula and flag it "lemma"',
    'proposition': 'plan to prove a formula and flag it "proposition"',
    }

# formulas and rules
formula_flags = ['theorem', 'proposition', 'lemma']    # must also appear in 'keywords'
class Formula:
    next_id = 0
    def __init__(self, expr, line, filename, status, flag=None, reason=None, comment=None):
        self.expr     = expr               # expression of the formula
        self.line     = line               # line of this formula
        self.filename = filename           # file of this formula
        self.status   = status             # one of 'use', 'assume', 'show', None (for derived)
        self.flag     = flag               # one of 'theorem' or 'lemma' or 'proposition' or etc or None
        self.reason   = reason             # the reason why it is true
        self.comment  = comment            # basically, a label of the formula
        self.id       = Formula.next_id    # a unique id for every formula
        Formula.next_id += 1

    def prefix_str(self):
        s = ''
        if self.status is not None:
            s += f'{self.status} '
        if self.flag is not None:
            s += f'{self.flag} '
        return s
    
    def comment_str(self):
        if self.comment is None:
            return ''
        else:
            return f' ; {self.comment}'
    
    def __str__(self):
        return f'{self.prefix_str()}{self.expr}{self.comment_str()}'

    def formula_str(self, kb):
        return f'{self.prefix_str()}{expr_str(self.expr, kb)}'

class Rule:
    next_id = 0
    def __init__(self, lhs, rhs, source_id):
        self.lhs       = lhs               # starting expression
        self.rhs       = rhs               # goal expression
        self.source_id = source_id         # formula id that implied this rule
        self.id        = Rule.next_id      # a unique id for every rule
        Rule.next_id += 1

# hierarchical knowledge base
# the level is increased inside blocks and files
# dropping a level drops also all local definitions
class KnowledgeBase():
    def __init__(self, parent=None, verbose=False):
        # general
        self.level    = 0 if parent is None else parent.level + 1
        self.parent   = parent

        # syntax
        self.infix    = {}        # left and right binding powers of infix operators
        self.postfix  = {}        # left binding power of postfix operator
        self.prefix   = {}        # right binding power of prefix operator
        self.brackets = {}        # keys are right brackets, values are left brackets
        self.arity    = {}        # for non-zero arities
        self.bindop   = {}        # for variable binding operators
        self.flat     = {}        # for declaring a flat operator, i.e. ($a + $b) + $c = $a + $b + $c
        self.sym      = {}        # for declaring a symmetric operator, i.e. $a + $b = $b + $a
        self.nud      = {}        # null denotation, entries are functions for parsing expressions
        self.led      = {}        # left denotation, entries are functions for parsing infix expressions
        self.lbp      = {}        # left binding power
        self.rbp      = {}        # right binding power
        self.bool     = {}        # dict of symbols declared to have boolean output
        self.var      = {}        # dict of variables with unused values
        self.const    = {}        # dict of constants with unused values
        self.alias    = {}        # dict of alias pointing to the original

        # theory
        self.theory   = []        # list of formulas (axioms added by 'use', 
                                  #                   assumptions added by 'assume',
                                  #                   and derived formulas)
        self.show     = []        # lists of formulas to show

        # misc
        self.format   = format_options[1] if parent is None else parent.format  # how formulas look in the shell
        self.verbose  = verbose if parent is None else parent.verbose           # extra information or not

    def entry_str(self, keyword, key, value):
        if   keyword == 'prefix':   return f'prefix "{key}" {value}'
        elif keyword == 'infix':    return f'infix "{key}" {value[0]} {value[1]}'
        elif keyword == 'postfix':  return f'postfix "{key}" {value}'
        elif keyword == 'brackets': return f'brackets "{value}" "{key}"'
        elif keyword == 'arity':    return f'arity "{key}" {value}'
        elif keyword == 'flat':     return f'flat "{key}"'
        elif keyword == 'sym':      return f'sym "{key}"'
        elif keyword == 'bindop':   return f'bindop "{key}"'
        elif keyword == 'bool':     return f'bool "{key}"'
        elif keyword == 'var':      return f'var "{key}"'
        elif keyword == 'const':    return f'const "{key}"'
        elif keyword == 'alias':    return f'alias "{key}" "{value}"'
        else: assert False, f'BUG: unknown keyword, got {keyword}'

    def dict_str(self, some_dict, keyword):
        return '\n'.join([self.entry_str(keyword, key, some_dict[key]) for key in some_dict])

    # SYNTAX RELATED
    def syntax_str(self):
        s = self.parent.syntax_str() if self.parent is not None else ''
        s += f'; syntax: declarations on level {self.level}\n'
        s += self.dict_str(self.prefix,   'prefix')
        s += self.dict_str(self.infix,    'infix')
        s += self.dict_str(self.postfix,  'postfix')
        s += self.dict_str(self.arity,    'arity')
        s += self.dict_str(self.bindop,   'bindop')
        s += self.dict_str(self.brackets, 'brackets')
        s += self.dict_str(self.flat,     'flat')
        s += self.dict_str(self.sym,      'sym')
        s += self.dict_str(self.bool,     'bool')
        return s

    is_infix   = lambda self, s: s in self.infix   or (self.parent is not None and self.parent.is_infix(s))
    is_prefix  = lambda self, s: s in self.prefix  or (self.parent is not None and self.parent.is_prefix(s))
    is_postfix = lambda self, s: s in self.postfix or (self.parent is not None and self.parent.is_postfix(s))
    is_bindop  = lambda self, s: s in self.bindop  or (self.parent is not None and self.parent.is_bindop(s))
    is_flat    = lambda self, s: s in self.flat    or (self.parent is not None and self.parent.is_flat(s))
    is_sym     = lambda self, s: s in self.sym     or (self.parent is not None and self.parent.sym(s))
    is_bool    = lambda self, s: s in self.bool    or (self.parent is not None and self.parent.is_bool(s))
    is_var     = lambda self, s: s in self.var     or (self.parent is not None and self.parent.is_var(s)) or s[0]=='$'
    is_const   = lambda self, s: s in self.const   or (self.parent is not None and self.parent.is_const(s))
    is_alias   = lambda self, s: s in self.alias   or (self.parent is not None and self.parent.is_alias(s))
    # constant vs variable symbols (variables start with '$')

    is_bracket = lambda self, s: s in self.brackets.values() or s in self.brackets.keys() or (self.parent is not None and self.parent.is_bracket(s))

    is_operator = lambda self, s: self.is_prefix(s) or self.is_infix(s) or self.is_postfix(s) or self.is_bracket(s)

    def get_arity(self, fun):
        if fun in self.arity:
            return self.arity[fun]
        else:
            return 0

    def add_arity(self, fun, a):
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

    def find_symbol(self, op):
        if self.is_prefix(op):    return 'prefix'
        elif self.is_infix(op):   return 'infix'
        elif self.is_postfix(op): return 'postfix'
        elif self.is_bracket(op): return 'bracket'
        else: assert False, f'BUG: call "find_symbol" only for existing symbols'

    def add_prefix(self, op, rbp):
        if self.is_operator(op) and not self.is_infix(op):    # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self.find_symbol(op)}')
        self.add_const(op)
        self.prefix[op] = rbp
        self.nud[op] = lambda ts, kb, op_token: [op_token, parse_expression(ts, kb, rbp)]

    def add_infix(self, op, lbp, rbp):
        if self.is_operator(op) and not self.is_prefix(op):   # infix and prefix at the same time is allowed
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self.find_symbol(op)}')
        self.add_const(op)
        self.infix[op] = (lbp, rbp)                           # to nicely list all operators
        self.led[op] = lambda ts, kb, left, op_token: [op_token, left, parse_expression(ts, kb, rbp)]
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_postfix(self, op, lbp):
        if self.is_operator(op):
            raise KurtException(f'EvalError: symbol "{op}" already exist as {self.find_symbol(op)}')
        self.add_const(op)
        self.postfix[op] = lbp                                # to nicely list all operators
        self.led[op] = lambda ts, kb, left, op_token: [op_token, left]
        self.lbp[op] = lbp                                    # for lbp lookup during parsing

    def add_bindop(self, fun):
        if fun not in self.arity:
            raise KurtException(f'EvalError: before declaring symbol "{fun}" as variable binding, you must set its arity')
        self.bindop[fun] = None

    def add_flat(self, op):
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator "{op}" must be infix operator to declare flatness')
        if self.is_flat(op):
            raise KurtException(f'EvalError: operator "{op}" is already declared "flat"')
        self.flat[op] = None

    def add_sym(self, op):
        if not self.is_infix(op):
            raise KurtException(f'EvalError: operator "{op}" must be infix operator to declare symmetry')
        if self.is_sym(op):
            raise KurtException(f'EvalError: operator "{op}" is already declared "sym"')
        self.sym[op] = None

    def add_brackets(self, lbracket, rbracket):
        if self.is_operator(lbracket):
            raise KurtException(f'EvalError: symbol "{lbracket}" already exist as {self.find_symbol(lbracket)}')
        if self.is_operator(rbracket):
            raise KurtException(f'EvalError: symbol "{rbracket}" already exist as {self.find_symbol(rbracket)}')
        self.add_const(lbracket)
        self.add_const(rbracket)
        self.brackets[rbracket] = lbracket    # to list the brackets (not used for parsing)
        def nud(ts, kb, _):
            expr = parse_expression(ts, kb, 0)
            token = next(ts)
            if token.value != rbracket: 
                raise KurtException(f'SyntaxError: expected "{rbracket}"', token.column)
            token.value = f'{lbracket} {rbracket}'    # use a value that can not come from the tokenizer
            return [token, expr]
        self.nud[lbracket] = nud
        self.lbp[rbracket] = bracket_lbp

    def add_var(self, s):
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a constant')
        self.var[s] = None        # add a key with value None

    def add_const(self, s):
        if self.is_var(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a variable or starts with $')
        self.const[s] = None      # add a key with value None

    def add_alias(self, s, t):
        if self.is_var(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a variable or starts with $')
        if self.is_const(s):
            raise KurtException(f'EvalError: symbol "{s}" is already a constant')
        if not (self.is_var(t) or self.is_const(t)):
            raise KurtException(f'EvalError: symbol "{t}" must be either a variable or a constant')
        self.alias[s] = t         # add a key `s` with value `t`

    def add_bool(self, s):
        if self.is_bool(s):
            raise KurtException(f'EvalError: symbol "{s}" is already declared bool')
        if not (self.is_var(s) or self.is_const(s)):
            raise KurtException(f'EvalError: symbol "{s}" must be either a variable or a constant')
        self.bool[s] = None       # add a key with value None

    def get_nud(self, token):
        if token.label == 'SYMBOL':
            if token.value in self.nud:
                return self.nud[token.value]
            elif self.parent is not None:
                return self.parent.get_nud(token)
        return lambda ts, kb, t: t   # the default

    def get_led(self, token):
        if token.label == 'SYMBOL':
            if token.value in self.led:
                return self.led[token.value]
            elif self.parent is not None:
                return self.parent.get_led(token)
        elif token.label == 'COMMENT':
            return lambda ts, kb, left, op_token: [op_token, left]   # same as for postfix
        raise KurtException(f'SyntaxError: infix or postfix operator expected, got {self.value}', token.column)

    def get_lbp(self, token):
        if token is None:
            raise KurtException(f'SyntaxError: expression expected, got end of line')
        if token.label == 'SYMBOL':
            if token.value in self.lbp:
                return self.lbp[token.value]
            elif self.parent is not None:
                return self.parent.get_lbp(token)
        elif token.label == 'COMMENT':
            return comment_lbp
        elif token.label == 'END':
            return end_lbp           # this is to finish the while loop in 'expression'
        # the default value
        return space_lbp         # this is used for 'f x y'

    # THEORY RELATED
    def all_theory(self):
        # iterate over all levels
        for f in self.theory:
            yield f
        if self.parent is not None:
            yield from self.parent.all_theory()

    def all_usable_implications(self):
        for f in self.all_theory():
            if is_implication(f.expr):
                yield f

    def all_usable_equations(self):
        for f in self.all_theory():
            if is_equation(f.expr):
                yield f

    def theory_str(self, keyword=None, op=None):
        s = self.parent.theory_str(keyword, op) if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.theory:
            if (keyword is None and op is None) or (keyword==f.status) or (keyword==f.flag) or is_op_expr(f.expr, op):
                s += f'{f.formula_str(self)}\n'
        return s

    def show_str(self):
        s = self.parent.show_str() if self.parent is not None else ''
        s += f'; on level {self.level}\n'
        for f in self.show:
            s += f'{f.formula_str(self)}\n'
        return s

# some important constants for the parser
bracket_lbp = 0                               # left binding power of brackets
end_lbp     = 0                               # left binding power of end of string
comment_lbp = 1                               # left binding power of comments
space_op    = ' '                             # must be something that is never returned from the tokenizer
space_lbp   = 22                              # left binding power: stronger than '='
space_rbp   = 22                              # right binding power: stronger than '='

# create initial knowledge base
initial_kb = KnowledgeBase()
initial_kb.add_infix("//", 3, 3)                       # substitution of variables
initial_kb.add_infix(',', 5, 5)                        # comma with binding power 1
initial_kb.add_infix('=', 20, 20)                      # equality with lower binding power than space
initial_kb.add_infix(space_op, space_lbp, space_rbp)   # the space operator is for expression like `f x`
initial_kb.add_flat(',')                               # flatness of comma operator
initial_kb.add_sym('=')                                # equalities should be symmetric
initial_kb.add_brackets('(', ')')                      # round brackets for grouping

################
## kurt lexer ##
################
class Token:
    def __init__(self, label, value, column=None):
        self.label  = label
        self.value  = value
        self.column = column
    def __repr__(self):
        return f'({self.label} "{self.value}")'
    def __lt__(self, other):
        return str(self.value) < str(other.value)   # note: this is not a good ordering on integers

## expressions
# an expression is either a token or a list of expressions
# instead of creating a class for expressions, we use the following functions
is_token = lambda expr: isinstance(expr, Token)
is_list  = lambda expr: isinstance(expr, list)

def expr_str(expr, kb):
    if kb.format == 'sexpr':
        return expr_sexpr(expr)
    elif kb.format == 'normal':
        return expr_normal(expr, kb)
    else:
        assert False, f'BUG: unknown expression format, got {kb.format}'

def expr_sexpr(expr):                      # create s-expression
    if is_token(expr):
        if expr.label == 'STRING':
            return f'"{expr.value}"'
        else:
            return str(expr.value)
    elif is_list(expr):
        return f'({" ".join([expr_sexpr(e) for e in expr])})'
    elif expr is None:
        return ''
    else:
        assert False, f'BUG: unknown expression, got {expr}'

def expr_normal(expr, kb, rbp=0):          # create raw input expression
    if is_token(expr):
        return expr_sexpr(expr)            # reuse implementation from expr_sexpr
    elif is_list(expr):
        lexpr = len(expr)
        if lexpr == 1:
            return expr_normal(expr[0], kb)
        elif lexpr == 2:
            a = expr[0].value
            if kb.is_prefix(a):
                return f'({a} {expr_normal(expr[1], kb)})'
            elif kb.is_postfix(a):
                return f'({expr_normal(expr[1], kb)} {a})'
            elif expr[0].label == 'COMMENT':
                return f'{expr_normal(expr[1], kb)} ; {a}'
            else:
                return f'{expr_normal(expr[0], kb)} {expr_normal(expr[1], kb)}'
        elif lexpr == 3:
            a = expr[0].value
            if kb.is_infix(a):
                return f'({expr_normal(expr[1], kb)} {a} {expr_normal(expr[2], kb)})'
            else:
                return f'({a} {expr_normal(expr[1], kb)} {expr_normal(expr[2], kb)})'
        else:
            a = expr[0].value
            if kb.is_flat(a):
                return f'({f' {a} '.join([expr_normal(e, kb) for e in expr[1:]])})'
            else:
                return f'({" ".join([expr_normal(e, kb) for e in expr])})'
    elif expr is None:
        return ''
    else:
        assert False, f'BUG: unknown expression, got {expr}'

def is_op_expr(e, op):
    return is_list(e) and is_token(e[0]) and e[0].value==op

is_equation    = lambda expr: is_op_expr(expr, '=')
is_implication = lambda expr: is_op_expr(expr, 'implies')

def equal_expr(t1, t2):                                  # equality for expressions
    # note: we assume that `flatness` and `symmetry` has been used to create normalized form
    if is_token(t1) and is_token(t2):                         # compare tokens
        return t1.label==t2.label and t1.value==t2.value
    elif is_list(t1) and is_list(t2) and len(t1)==len(t2):    # compare lists
        return all([equal_expr(a, b) for (a,b) in zip(t1, t2)])
    else:                                                     # token and list are always non-equal
        return False

def compare_expr(t1, t2):                                # "less than" for expressions
    if is_token(t1) and is_list(t2):
        return -1                                        # e.g. 17 < [1,2]
    elif is_list(t1) and is_token(t2):
        return 1                                         # e.g. [1,2] < 17
    elif t1 < t2:
        return -1                                        # e.g. 17 < 42 or [1,2,3] < [55]
    elif t1 > t2:
        return 1                                         # e.g. 42 > 17 or [55] > [1,2,3]
    else:
        return 0                                         # e.g. 42 == 42 or [1,2,3] == [1,2,3]

def simplify(expr, kb):
    if expr is None:
        return None
    for op in kb.flat: 
        expr = flatten_op(op, expr)       # flatten certain operators
    expr = sort_symmetric_ops(kb, expr)   # sort expressions of symmetric operators from the inside to the outside
    return expr

# special tokens that are made for the parser and sometimes artificially generated
space_token = Token('SYMBOL', ' ')      # for expressions like 'f x'
end_token   = Token('END', '')          # for the end of a string

# scanner based on regular expressions (let's support unicode!)
# note that the ordering of the expressions here is important
scanner = re.compile(r'''
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

def scan_string(input_line):

    # setup current location
    lastpos = 0        # for calculating the column number, update after a newline
    for match in scanner.finditer(input_line):
        
        # extract the information from the match
        label  = match.lastgroup           # name of the group
        value  = match.groupdict()[label]  # the value, somewhat complicated code, but necessary for counting the indents
        pos    = match.start()             # position in s
        column = pos - lastpos             # column of the match

        # create tokens
        if   label == 'COMMENT':           # remove leading semicolon and space at beginning and end
            yield Token(label, value[1:].strip(), column + len(value))
        elif label == 'WHITE':
            continue                       # whitespace is ignored
        elif label == 'SYMBOL':
            yield Token(label, value, column + len(value))
        elif label == 'INT':
            yield Token(label, int(value), column + len(value))
        elif label == 'FLOAT':
            yield Token(label, float(value), column + len(value))
        elif label == 'STRING':
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

class PG(object):                                 # a peekable generator
    def __init__(self, gen):
        self.gen  = gen                           # the generator
        self.eog  = False                         # end-of-generator, are we done yet?
        self.peek = None                          # initial peek is None
        self.__next__()                           # possibly modifies self.eog
    def __iter__(self):
        return self
    def __next__(self):
        if self.eog:
            raise StopIteration
        p = self.peek                             # the peek gets returned
        try:
            self.peek = next(self.gen)            # update the peek
        except StopIteration:                     # delay the exception until the next 'next'-call
            self.peek = None                      # nothing to peek anymore
            self.eog = True                       # next call __next__ triggers the exception
        return p

# by replacing aliases as early as possible, we don't have to register the alias as infix, etc
def replace_alias(kb, token):
    if token.label == 'SYMBOL' and token.value in kb.alias:
        token.value = kb.alias[token.value]
    return token

# the heart of the Pratt parser (calls 'led' and 'nud' implemented elsewhere in this file)
def parse_expression(ts, kb, rbp):
    t = next(ts)                                  # get next token
    t = replace_alias(kb, t)                      # replace alias
    nud = kb.get_nud(t)                           # get the correct 'nud' function
    left = nud(ts, kb, t)                         # nud == "null denotation"
    peek_lbp = kb.get_lbp(ts.peek)                # peek at lbp of the next token
    while rbp < peek_lbp:                         # is the next operator binding more strongly?
        if peek_lbp == space_rbp:                 # not another operator but another expression
            t = space_token                       # insert special token for expression like 'f x'
        else:                                     # peek_lbp is larger or smaller than space_rbp
            t = next(ts)                          # get next token
        led = kb.get_led(t)                       # get the correct 'led' function
        left = led(ts, kb, left, t)               # led == "left denotation"
        peek_lbp = kb.get_lbp(ts.peek)            # update peek_lbp for the iteration
    return left                                   # return the accumulated expression

def parse_tokenlist(expr_list, kb):
    tokenlist = expr_list + [end_token]           # add end token for parse_expression
    ts = PG((t for t in tokenlist))               # turn list into peekable generator
    expr = parse_expression(ts, kb, 0)            # parse the tokenlist
    return post_process(kb, expr)[0]              # turn spaces into calls

def sort_symmetric_ops(kb, expr):                        # symmetric operators can sort their args
    if is_list(expr):
        expr = [sort_symmetric_ops(kb, e) for e in expr] # start inside
        if is_token(expr[0]) and expr[0].label == 'SYMBOL' and expr[0].value in kb.sym:
            expr = [expr[0]] + sorted(expr[1:], key=functools.cmp_to_key(compare_expr))
        return expr
    elif is_token(expr):
        return expr
    else:
        assert False, f'BUG: expression must be list or Token, got {expr}'

def flatten_op(op, expr):                                # flatten nested 'op'-expressions
    # e.g. [',', 17, [',', 42, 100]] --> [',', 17, 42, 100]
    if is_token(expr):
        return expr
    elif is_list(expr):
        if is_op_expr(expr, op):
            e = [expr[0]]
            for i in range(1, len(expr)):
                ee = flatten_op(op, expr[i])
                if is_op_expr(ee, op):
                    e.extend(ee[1:])
                else:
                    e.append(ee)
            return e
        else:
            return [flatten_op(op, e) for e in expr]
    else:
        assert False, f'BUG: expression must be list or Token, got {expr}'

def group_by_arity(kb, expr):
    assert is_op_expr(expr, ' '), f'BUG: expected space-operator, got {expr}'
    assert len(expr) > 1, f'BUG: got empty expr'
    e = []
    while len(expr) > 1:
        x = expr.pop()                                          # start at the end
        if is_token(x) and x.label == 'SYMBOL':                 # only symbols have args
            arity = kb.get_arity(x.value)                       # get arity
            if arity > 0:                                       # do we expect args?
                try:
                    x = [x] + [e.pop() for i in range(arity)]   # collect the args
                except IndexError:
                    raise KurtException(f'EvalError: not enough arguments for "{x.value}"')
        e.append(x)
    e.reverse()
    return e

def process_arity(kb, expr):
    if is_token(expr):
        return expr
    elif is_list(expr):
        if is_op_expr(expr, ' '):
            expr = group_by_arity(kb, expr)
        return [process_arity(kb, e) for e in expr]
    else:
        assert False, f'BUG: list or Token expected, got {expr}'

def remove_round_brackets(expr):
    if is_token(expr):
        return expr
    elif is_list(expr):
        if is_op_expr(expr, '( )'):
            return remove_round_brackets(expr[1])
        else:
            return [remove_round_brackets(e) for e in expr]
    else:
        assert False, f'BUG: list or Token expected, got {expr}'

def check_no_keywords(expr):                             # keywords inside the expression are forbidden
    if is_token(expr):
        if expr.value in keywords:
            raise KurtException(f'SyntaxError: keywords not allowed inside expressions', expr.column)
    elif is_list(expr):
        for e in expr:
            check_no_keywords(e)
    else:
        assert False, f'BUG: list or Token expected, got {expr}'

def post_process(kb, expr):
    match expr:
        case Token(label='COMMENT', value=comment):
            return None, comment
        case Token():
            return expr, None
        case [Token(label='COMMENT', value=comment), e]:
            expr = e
        case _:
            comment = None
    check_no_keywords(expr)                          # no keywords allowed in expressions
    expr = flatten_op(' ', expr)                     # flatten all space operators
    expr = process_arity(kb, expr)                   # turns space operators into function calls according to arities
    expr = remove_round_brackets(expr)               # remove round brackets for grouping
    return expr, comment

def parse_tokenstream(ts, kb):                           # gets a peekable token stream
    # returns an expression and a comment
    if ts.peek.label == 'END': 
        return None, None                                # empty token stream
    elif ts.peek.value in keywords:
        # we have to remove the comment already here, so that commands like `bool` get not confused
        match list(ts):
            case [*rest, Token(label='COMMENT', value=comment), end_token]:
                return rest, comment
            case [Token(label='COMMENT', value=comment), end_token]:
                return None, comment
            case [*rest, end_token]:
                return rest, None                        # chop off the end-token and postpone the parsing
    else:
        expr = parse_expression(ts, kb, 0)               # parse expression
        return post_process(kb, expr)                    # apply some transformations

## kurt eval
def create_usage(keyword, arg_labels):
    s = ''
    for arg_label in arg_labels:
        s += f'    {keyword}'
        for l in arg_label:
            s += f' {l}'
        s += f'\n'
    return s

def check_args(expr, arg_labels):
    # e.g. 'check_args(expr, [[], ['SYMBOL', 'INT']], ['list', 'add'])
    # where [] implies none is possible
    # where ['SYMBOL', 'INT'] implies two args with symbol and integer are possible as well
    assert is_token(expr[0]), f'BUG: token expected, got {expr[0]}'
    msg = create_usage(expr[0].value, arg_labels)
    for arg_label in arg_labels:
        if len(expr) == len(arg_label) + 1:
            for (e, l) in zip(expr[1:], arg_label):
                if l != 'EXPR':                    # expressions are just fine
                    if not is_token(e) or e.label != l:
                        raise KurtException(f'EvalError: wrong argument types, possible is:\n{msg}', e.column)
            return       # we found a correct number of arguments and checked all labels
    if ['EXPR'] not in arg_labels:
        raise KurtException(f'EvalError: wrong number of arguments, possible is:\n{msg}', expr[0].column)

def strip_keyword(s, column):
    return s[(1+column):]                  # get rid of the keyword at the beginning

def eval_expression(expr, kb, line, filename, comment):
    if expr is None:
        return kb
    if is_token(expr):
        value, label = expr.value, expr.label
    elif is_token(expr[0]):
        value, label = expr[0].value, expr[0].label
    else:
        raise KurtException(f'SyntaxError: token or list beginning with a token expected, got {expr}')

    # KEYWORD
    if value in keywords and label == 'SYMBOL':
        keyword = value
        if is_token(expr):
            expr = [expr]

        # GENERAL STUFF
        if keyword == 'help':
            check_args(expr, [[]])
            for k in keywords.keys(): print(f'  {k:<12} {keywords[k]}')
        elif keyword == 'load':
            check_args(expr, [['STRING']])
            kb = load_file(expr[1].value, kb)
        elif keyword == 'parse':
            check_args(expr, [['EXPR']])
            e = parse_tokenlist(expr[1:], kb)
            if e is None:
                print(f'; {comment}')
            else:
                e = simplify(e, kb)               # simplify the formula using flatness and symmetry
                if comment is None:
                    print(f'{expr_str(e, kb)}')
                else:
                    print(f'{expr_str(e, kb)} ; {comment}')
        elif keyword == 'format':
            check_args(expr, [[], ['SYMBOL']])
            if len(expr) == 1: print(kb.format)
            elif len(expr) != 2 or not is_token(expr[1]) or not expr[1].value in format_options:
                raise KurtException(f'only {format_options} are allowed')
            else:
                kb.format = expr[1].value
        elif keyword == 'level':
            check_args(expr, [[]])
            print(kb.level)

        # SYNTAX RELATED
        elif keyword == 'syntax':
            check_args(expr, [[]])
            print(kb.syntax_str())
        elif keyword == "prefix":
            check_args(expr, [[], ['STRING', 'INT']])
            if   len(expr) == 1: print(kb.dict_str(kb.prefix, keyword))
            elif len(expr) == 3: kb.add_prefix(expr[1].value, expr[2].value)
        elif keyword == "postfix":
            check_args(expr, [[], ['STRING', 'INT']])
            if   len(expr) == 1: print(kb.dict_str(kb.postfix, keyword))
            elif len(expr) == 3: kb.add_postfix(expr[1].value, expr[2].value)
        elif keyword == "infix":
            check_args(expr, [[], ['STRING', 'INT', 'INT']])
            if   len(expr) == 1: print(kb.dict_str(kb.infix, keyword))
            elif len(expr) == 4: kb.add_infix(expr[1].value, expr[2].value, expr[3].value)
        elif keyword == "arity":
            check_args(expr, [[], ['STRING', 'INT'], ['SYMBOL', 'INT']])
            if   len(expr) == 1: print(kb.dict_str(kb.arity, keyword))
            elif len(expr) == 3: kb.add_arity(expr[1].value, expr[2].value)
        elif keyword == "brackets":
            check_args(expr, [[], ['STRING', 'STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.brackets, keyword))
            elif len(expr) == 3: kb.add_brackets(expr[1].value, expr[2].value)
        elif keyword == "bindop":
            check_args(expr, [[], ['STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.bindop, keyword))
            elif len(expr) == 2: kb.add_bindop(expr[1].value)
        elif keyword == 'flat':
            check_args(expr, [[], ['STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.flat, keyword))
            elif len(expr) == 2: kb.add_flat(expr[1].value)
        elif keyword == 'sym':
            check_args(expr, [[], ['STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.sym, keyword))
            elif len(expr) == 2: kb.add_sym(expr[1].value)
        elif keyword == 'bool':
            check_args(expr, [[], ['STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.bool, keyword))
            elif len(expr) == 2: kb.add_bool(expr[1].value)
        elif keyword == 'var':
            check_args(expr, [[], ['STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.var, keyword))
            elif len(expr) == 2: kb.add_var(expr[1].value)
        elif keyword == 'const':
            check_args(expr, [[], ['STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.const, keyword))
            elif len(expr) == 2: kb.add_const(expr[1].value)
        elif keyword == "alias":
            check_args(expr, [[], ['STRING', 'STRING']])
            if   len(expr) == 1: print(kb.dict_str(kb.alias, keyword))
            elif len(expr) == 3: kb.add_alias(expr[1].value, expr[2].value)

        # THEORY AND PROOF RELATED
        elif keyword == 'theory':
            check_args(expr, [[]])
            print(kb.theory_str())
        elif keyword == "equations":
            check_args(expr, [[]])
            print(kb.theory_str(op='='))
        elif keyword == "implications":
            check_args(expr, [[]])
            print(kb.theory_str(op='implies'))
        elif keyword in ['use', 'assume']:
            check_args(expr, [[], ['EXPR']])
            if len(expr) == 1: print(kb.theory_str(keyword=keyword))
            else:
                e = parse_tokenlist(expr[1:], kb)
                if not bool_expr(e, kb):
                    raise KurtException(f'ProofError: used/assumed expression must evaluate to boolean')
                e = simplify(e, kb)               # simplify the formula using flatness and symmetry
                reason = {'use': 'axiom', 'assume': 'assumption'}[keyword]
                if comment is not None:
                    reason += f' {comment}'
                f = Formula(e, line, filename, status=keyword, reason=reason, comment=comment)
                kb.theory.append(f)
                log(f.formula_str(kb), f'{line} {reason}', kb)
        elif keyword in ['show'] + formula_flags:
            check_args(expr, [[], ['EXPR']])
            if len(expr) == 1: print(kb.show_str())
            else:
                e = parse_tokenlist(expr[1:], kb)
                if not bool_expr(e, kb):
                    raise KurtException(f'ProofError: expression to show must evaluate to boolean')
                e = simplify(e, kb)               # simplify the formula using flatness and symmetry
                flag = None if keyword=='show' else keyword
                f = Formula(e, line, filename, status='show', flag=flag, comment=comment)  # syntactic sugar for theorem, proposition, lemma
                kb.show.append(f)
                reason = f'{line} claim'
                if comment is not None:
                    reason += f' {comment}'
                log(f.formula_str(kb), reason, kb)
        elif keyword == 'proof':                  # opens a new block (scope)
            check_args(expr, [[]])
            if len(kb.show) == 0:
                raise KurtException(f'ProofError: can not start proof since there is no planned formula on current level')
            log('proof', None, kb)
            kb = KnowledgeBase(kb)                # add a new level/scope to the knowledgebase
        elif keyword == 'qed':                    # closes the last block (scope)
            check_args(expr, [[]])
            if kb.level == 0:
                raise KurtException(f'EvalError: no block to close')
            if len(kb.show) > 0:                  # any planned formulas inside the current proof?
                raise KurtException(f'ProofError: planned formula "{pf}" in current proof is unproven')
            assert len(kb.parent.show) > 0, f'BUG: no planned formula on previous level, this should have been already checked when calling "proof"'
            pf = kb.parent.show[-1]               # peek at the last planned formula from previous level
            reason = impl_intro(pf.expr, kb)      # this might generate a KurtException
            kb = kb.parent                        # drop current level
            f = Formula(pf.expr, line, filename, status=None, flag=pf.flag, reason=reason)
            kb.show.pop()                         # pop it now off the show stack, since it was proved
            kb.theory.append(f)                   # add a copy to the theory
            log('qed', None, kb)
            log(f.formula_str(kb), f'{line} {reason}', kb)
        else:
            assert False, f'BUG: unknown keyword, got "{keyword}"'

    # everything else: try to derive the formula and add it to the theory
    else:
        if not bool_expr(expr, kb):
            raise KurtException(f'ProofError: expression must evaluate to boolean')
        expr = simplify(expr, kb)                 # simplify the formula using flatness and symmetry
        reason = derive_expr(expr, kb)            # this might raise ProofError exceptions
        f = Formula(expr, line, filename, status=None, reason=reason)
        kb.theory.append(f)                         # add it to the knowledge base
        log(f.formula_str(kb), f'{line} {reason}', kb)

    # finally return the possibly modified knowledgebase
    return kb

#################
## kurt prover ##
#################
# the strategy:
# - list of rules with LHS and RHS
# - check for an expr whether it matches the RHS (is the match unique)?  can we get the list of all matches?  use yield!
# - using the match, instantiate the LHS and look for formulas in the theory until all formulas in the LHS are matched
# - possibly there are hints to quickly find the right formulas of the LHS
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

def debug(s):
    print(s)

def log(s, reason, kb):
        indent = ' ' * (proof_indent * kb.level)
        if reason is None:
            print(indent+s)
        else:
            print(f'{(indent+s):<60}; {reason}')

def bool_expr(expr, kb):
    match expr:
        case Token(label='SYMBOL', value=v):
            return kb.is_bool(v)
        case [Token(label='SYMBOL', value=v), *rest]:
            return kb.is_bool(v)
    return False

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

def top_intro(e):
    # <nothing>
    # -----
    # true
    if is_token(e) and e.label == 'SYMBOL' and e.value == 'true':
        return 'top_intro'
    else:
        return None

def equal_intro(e):
    # <nothing>
    # -----
    # True
    if is_list(e) and len(e) == 3 and equal_expr(e[1], e[2]):
        return 'equal_intro'
    else:
        return None

def restatement(e, kb):
    # A
    # -----
    # A
    for ff in kb.all_theory():
        if equal_expr(ff.expr, e):
            return 'restatement'
    return None

# this function is only called when closing a block (via `qed` or using indentation)
def impl_intro(expr, kb):
    
    # step 1: collect all assumptions of the current level
    premise = [f.expr for f in kb.theory if f.status=='assume']
    if len(kb.theory) == 0:
        raise KurtException(f'ProofError: nothing was shown in the (sub-)proof')
    last_formula = kb.theory[-1]
    if last_formula.status != None:
        raise KurtException(f'ProofError: last formula in a (sub-)proof can not have `show`, `assume`, `use` status')
    conclusion = last_formula.expr        # last element is the conclusion

    # step 2: form a formula using the last formula in the current level
    reason = 'by impl-intro (last proof)'
    if len(premise) == 0:                  # just the conclusion (empty premise)
        result = conclusion
        reason = 'by last proof'
    else:
        if len(premise) == 1:              # premise is one formula
            premise = premise[0]
        else:                              # premise is conjunctive
            premise = simplify([Token(label='SYMBOL', value='and')] + premise, kb)
        result = [Token(label='SYMBOL', value='implies'), premise, conclusion]   # construct implication

    # step 3: compare against the planned expression `expr`
    if equal_expr(expr, result):
        if kb.verbose:
            print(f'goal    {expr}')
            print(f'derived {result}')
        return reason
    raise KurtException(f'ProofError: could not prove    {expr}\n            instead got        {result}')

def equal_elim(e, kb):
    pass
    #assert False, f'BUG: equal_elim is not implemented yet'

## WE ARE IGNORING FOR NOW WHETHER VARIABLES ARE BOUND OR FREE

def apply_subst(e, subst, kb):
    match e:
        case Token(label='SYMBOL', value=v) if kb.is_var(v) and v in subst:
            return subst[v]
        case [*children]:
            return [apply_subst(child, subst, kb) for child in children]
        case _:
            return e

# `match_one` matches a single expression to a single pattern
def match_one(pattern, expr, subst, kb):
    assert isinstance(pattern, Token | list), f'BUG: `match_one` must be called with an expression as the pattern, not with a formula'
    assert isinstance(expr, Token | list), f'BUG: `match_one` must be called with an expression, not with a formula'
    # matches the `expr` to the `pattern` and extends the `subst` (substitutions/bindings)
    match pattern:
        case Token(label='SYMBOL', value=v) if kb.is_var(v):
            assert v not in subst, f'BUG: variable "{v}" is already in the substitution, infinite regression?'
            subst[v] = expr      # extend the substitution
            return subst
        case Token(label=l, value=v) if is_token(expr) and l==expr.label and v==expr.value:
            return subst
        case [*_] if is_list(expr) and len(pattern)==len(expr):
            for (p,e) in zip(pattern, expr):
                p = apply_subst(p, subst, kb)
                if (subst:=match_one(p, e, subst, kb)) is None:
                    return None     # no match
            return subst
    return None           # no match, so no `subst` dictionary

# match_all matches a list of formulas to the theory
def match_all(premises, subst, kb):
    assert all([isinstance(p, Token | list) for p in premises]), f'BUG: `match_all` must be called with lists of expressions, not formulas'
    match premises:
        case []:
            return subst     # done!
        case [premise, *rest]:
            premise = apply_subst(premise, subst, kb)
            for candidate in kb.all_theory():    # iterate over all formulas
                # we use `subst_tmp` to avoid overwriting `subst` for the `continue`
                if (subst_tmp := match_one(candidate.expr, premise, subst, kb)) is None:
                    continue   # no match of the `premise`
                return match_all(rest, subst_tmp, kb)
            return None
    assert False, f'BUG: `match_all` must be called with a list'

def derive_expr(e, kb):

    # check hard-coded rules
    if (reason:=top_intro(e)):       return reason
    if (reason:=equal_intro(e)):     return reason
    if (reason:=restatement(e, kb)): return reason
    if (reason:=equal_elim(e, kb)):  return reason

    # check user-defined rules
    for implication in kb.all_usable_implications():
        conclusion = implication.expr[2]
        if (subst := match_one(conclusion, e, {}, kb)) is None:
            continue   # no luck this time, try the next iteration
        # match was found with conclusion, unpack the premises
        match implication.expr[1]:
            case [Token(label='SYMBOL', value='and'), *premises]:
                pass    # assigned already `premises` in the case matching
            case premise:
                premises = [premise]    # wrap a single premise in a list
        # check the premises
        if (subst := match_all(premises, subst, kb)) is None:
            continue   # no luck this time, try the next iteration
        if kb.verbose:
            print('BINGO!')
            print(f'expression to prove: {expr_str(e, kb)}')
            print(f'implication used:    {implication.formula_str(kb)}')
            print(f'substitution used:   {subst}')
        if implication.comment is not None:
            reason = f'by {implication.comment}'
        else:
            reason = f'by {implication.line}'
        return reason    # bingo!  found an implication

    # couldn't derive formula using any of the rules
    raise KurtException(f'ProofError: can not derive expression')

###########################
## commandline interface ##
###########################

def eval(input_line, kb, line, filename):
    try:
        ts            = PG(scan_string(input_line))                        # lexer
        expr, comment = parse_tokenstream(ts, kb)                          # parser
        kb            = eval_expression(expr, kb, line, filename, comment) # evaluation
    except KurtException as e:
        if e.column is None: e.column = len(input_line)
        if filename == '<stdin>':
            msg = f'\n'
        else:
            msg = f'  File "{filename}", line {line}\n'
        msg += f'    {input_line}\n'
        msg += f'    {" " * e.column + "^"}\n'
        msg += e.msg
        print(msg, file=sys.stderr)
    return kb

def load_file(filename, kb, markdown=False):
    # files are always loaded into level
    level = kb.level       # save current level
    if not filename.endswith('.kurt'):
        filename += '.kurt'
    try:
        filename = find_theory_file(filename)    # search along the path
        if filename is None:
            raise OSError
        with open(filename) as f:
            kb = read_eval_loop(f, kb, markdown)
    except OSError as e:
        # we have to add `from None` to avoid exception chaining, since we only want to see the KurtException
        raise KurtException(f'EvalError: unable to open "{filename}"') from None
    # after running the file all blocks must be closed
    if kb.level != level:
        kb.level = level       # set levels back before raising the exception
        raise KurtException(f'EvalError: inside "{filename}" not all blocks closed, missing "end"?')
    log(f'Loaded "{filename}"', None, kb)
    return kb

def prompt(level, line, continued=False):
    s = '> ' * level
    if continued:
        s += f'...[{line}] '                        # line continuation
    else:
        s += f'!!![{line}] '                        # the bangs mean "show!"
    return s

def read_eval_loop(input_stream, kb, markdown=False):
    not_file   = (input_stream.name == '<stdin>')   # for non files we have a fancy prompt
    line       = 1
    continued  = False
    input_line = ''
    if not_file:
        readline.parse_and_bind("tab: complete")    # Enable tab completion

    while True:
        try:
            if not_file:
                prompt_text = prompt(kb.level, line, continued)
                new_line = input(prompt_text).rstrip()  # use readline
                readline.add_history(new_line)          # save to history
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
                kb = eval(input_line, kb, line, input_stream.name)
                input_line = ''  # Reset input
                continued = False
                line += 1
        except EOFError:
            print("\nBye!")
            break
    
    return kb

def find_theory_file(fname):
    for p in theory_path:
        cand = os.path.join(p, fname)
        if os.path.isfile(cand):
            return cand
    return None

def parse_args():
    parser = argparse.ArgumentParser(description=f'a simple proof assistant ({made_by})')
    parser.add_argument("filename", nargs='?',                       help=f'check the proof in the file, w/o filename start interactively')
    parser.add_argument('-i', '--interactive',  action='store_true', help=f'enter read-eval-print loop after loading `filename`')
    parser.add_argument('-m', '--markdown',     action='store_true', help=f'run on `.md` files instead of `.kurt`, will ignore everything that is not indented by {md_indent} spaces')
    parser.add_argument('-p', '--path',                              help=f'specify the path where `load` looks for theories after checking `.`')
    parser.add_argument('-v', '--verbose',      action='store_true', help=f'show extra information during proof checking')
    parser.add_argument('-t', '--test',         action='store_true', help=f'run tests')
    return parser.parse_args()

def main():
    args = parse_args()
    print(f'This is Kurt, Version {version} ({made_by})')

    # the knowledge base we start with on level 0
    kb = initial_kb

    # verbosity?
    kb.verbose = args.verbose
    
    # run tests?
    if args.test:
        import unittest
        from test import kurt_test
        suite = unittest.TestLoader().loadTestsFromModule(kurt_test)
        unittest.TextTestRunner(verbosity=2).run(suite)
        # from https://stackoverflow.com/questions/31559473/run-unittests-from-a-different-file
        exit(0)

    # theory path
    if args.path is not None:
        theory_path[1] = args.path   # overwrite the default 'theory'

    # by default load `default_theory` or nothing
    if (theory_filename := find_theory_file(default_theory)):
        kb = eval(f'load "{theory_filename}"', kb, 0, '<stdin>')

    # if there is a filename run the file
    if args.filename is not None:
        kb = eval(f'load "{args.filename}"', kb, 0, '<stdin>')
    else:
        args.interactive = True

    # read-eval-print loop
    if args.interactive:
        kb = read_eval_loop(sys.stdin, kb)
    exit(0)

if __name__ == "__main__":
    main()
