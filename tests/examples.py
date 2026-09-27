## examples to test lexing and parsing

# three entries: input, scanned, parsed
examples = [
    # left associative
    ("1 - 1 + 1",
     '[(INT "1"), (SYMBOL "-"), (INT "1"), (SYMBOL "+"), (INT "1"), (END "$$$")]',
     "(+ 1 (- 1 1))"),
    # left associative
    ("(1 - 1) + 1",
     '[(SYMBOL "("), (INT "1"), (SYMBOL "-"), (INT "1"), (SYMBOL ")"), (SYMBOL "+"), (INT "1"), (END "$$$")]',
     "(+ 1 (- 1 1))"),
    # right associative
    ("1 - (1 + 1)",
     '[(INT "1"), (SYMBOL "-"), (SYMBOL "("), (INT "1"), (SYMBOL "+"), (INT "1"), (SYMBOL ")"), (END "$$$")]',
     "(- 1 (+ 1 1))"),
    # left associative
    ("12 / 3 / 4",
     '[(INT "12"), (SYMBOL "/"), (INT "3"), (SYMBOL "/"), (INT "4"), (END "$$$")]',
     "(/ (/ 12 3) 4)"),
    # simple sum
    ("17 + 42",
     '[(INT "17"), (SYMBOL "+"), (INT "42"), (END "$$$")]',
     "(+ 17 42)"),
    # simple sum with flatness
    ("17 + 42 + 100",
     '[(INT "17"), (SYMBOL "+"), (INT "42"), (SYMBOL "+"), (INT "100"), (END "$$$")]',
     "(+ 100 17 42)"),
    # unary minus
    ("-1",
     '[(SYMBOL "-"), (INT "1"), (END "$$$")]',
     "(- 1)"),
    # function call
    ("x (-1)",
     '[(SYMBOL "x"), (SYMBOL "("), (SYMBOL "-"), (INT "1"), (SYMBOL ")"), (END "$$$")]',
     "(x (- 1))"),
    # assign
    ("x = 1",
     '[(SYMBOL "x"), (SYMBOL "="), (INT "1"), (END "$$$")]',
     "(= x 1)"),
    # assign with unary minus
    ("x = -1",
     '[(SYMBOL "x"), (SYMBOL "="), (SYMBOL "-"), (INT "1"), (END "$$$")]',
     "(= x (- 1))"),
    # unary minus in sum with flatness
    ("-1 + 18 + -15",
     '[(SYMBOL "-"), (INT "1"), (SYMBOL "+"), (INT "18"), (SYMBOL "+"), (SYMBOL "-"), (INT "15"), (END "$$$")]',
     "(+ 18 (- 1) (- 15))"),
    # unary minus in product
    ("3 * -5",
     '[(INT "3"), (SYMBOL "*"), (SYMBOL "-"), (INT "5"), (END "$$$")]',
     "(* 3 (- 5))"),
    # "*-" is unknown operator
    ("3 *- 5",
     '[(INT "3"), (SYMBOL "*-"), (INT "5"), (END "$$$")]',
     "(3 *- 5)"),
    # simple postfix
    ("17!",
     '[(INT "17"), (SYMBOL "!"), (END "$$$")]',
     "(! 17)"),
    # function call
    ("f 18",
     '[(SYMBOL "f"), (INT "18"), (END "$$$")]',
     "(f 18)"),
    # function call binds less than most other stuff
    ("f 18 + 42",
     '[(SYMBOL "f"), (INT "18"), (SYMBOL "+"), (INT "42"), (END "$$$")]',
     "(+ 42 (f 18))"),
    # function call is left associative
    ("f 178 42",
     '[(SYMBOL "f"), (INT "178"), (INT "42"), (END "$$$")]',
     "(f 178 42)"),
    # function call with sum
    ("f 178 + 432 422",
     '[(SYMBOL "f"), (INT "178"), (SYMBOL "+"), (INT "432"), (INT "422"), (END "$$$")]',
     "(+ (432 422) (f 178))"),
    # two function calls
    ("f (2) (3)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "2"), (SYMBOL ")"), (SYMBOL "("), (INT "3"), (SYMBOL ")"), (END "$$$")]',
     "(f 2 3)"),
    # product before sum
    ("a + b * c",
     '[(SYMBOL "a"), (SYMBOL "+"), (SYMBOL "b"), (SYMBOL "*"), (SYMBOL "c"), (END "$$$")]',
     "(+ a (* b c))"),
    # product before sum
    ("a * b + c",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "b"), (SYMBOL "+"), (SYMBOL "c"), (END "$$$")]',
     "(+ c (* a b))"),
    # sum before product with brackets
    ("a * (b + c)",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "("), (SYMBOL "b"), (SYMBOL "+"), (SYMBOL "c"), (SYMBOL ")"), (END "$$$")]',
     "(* a (+ b c))"),
    # 
    ("f3 1 2 3",
     '[(SYMBOL "f3"), (INT "1"), (INT "2"), (INT "3"), (END "$$$")]',
     "(f3 1 2 3)"),
    # 
    ("f3 1 2+4 3",
     '[(SYMBOL "f3"), (INT "1"), (INT "2"), (SYMBOL "+"), (INT "4"), (INT "3"), (END "$$$")]',
     "(+ (4 3) (f3 1 2))"),
    # one function call
    ("f (17)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "17"), (SYMBOL ")"), (END "$$$")]',
     "(f 17)"),
    # one function call
    ("f (17, 42)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "17"), (SYMBOL ","), (INT "42"), (SYMBOL ")"), (END "$$$")]',
     "(f (, 17 42))"),
    # one function call
    ("f 17",
     '[(SYMBOL "f"), (INT "17"), (END "$$$")]',
     "(f 17)"),
    # one function call
    ("f 17 42",
     '[(SYMBOL "f"), (INT "17"), (INT "42"), (END "$$$")]',
     "(f 17 42)"),
    # one function call
    ("f (17, 42)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "17"), (SYMBOL ","), (INT "42"), (SYMBOL ")"), (END "$$$")]',
     "(f (, 17 42))"),
    # one function call
    ("f(a, b)",
     '[(SYMBOL "f"), (SYMBOL "("), (SYMBOL "a"), (SYMBOL ","), (SYMBOL "b"), (SYMBOL ")"), (END "$$$")]',
     "(f (, a b))"),
    # 
    ("1 key1 2+3 key2",
     '[(INT "1"), (SYMBOL "key1"), (INT "2"), (SYMBOL "+"), (INT "3"), (SYMBOL "key2"), (END "$$$")]',
     "(+ (1 key1 2) (3 key2))"),
    # sum of two bracket expressions
    ("(a b) + (c d)",
     '[(SYMBOL "("), (SYMBOL "a"), (SYMBOL "b"), (SYMBOL ")"), (SYMBOL "+"), (SYMBOL "("), (SYMBOL "c"), (SYMBOL "d"), (SYMBOL ")"), (END "$$$")]',
     "(+ (a b) (c d))"),
    # space binds stronger than comma
    ("f (a, b c, d), e",
     '[(SYMBOL "f"), (SYMBOL "("), (SYMBOL "a"), (SYMBOL ","), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL ","), (SYMBOL "d"), (SYMBOL ")"), (SYMBOL ","), (SYMBOL "e"), (END "$$$")]',
     "(f (, a (b c) d))"),
    # two expressions
    ("a * b c + d",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL "+"), (SYMBOL "d"), (END "$$$")]',
     "(+ d (* a (b c)))"),
    # equality vs space
    ("a = b c d = e",
     '[(SYMBOL "a"), (SYMBOL "="), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL "d"), (SYMBOL "="), (SYMBOL "e"), (END "$$$")]',
     "(and (= a (b c d)) (= (b c d) e))"),
    # parentheses keep a relation from chaining
    ("(a = b) = c",
     '[(SYMBOL "("), (SYMBOL "a"), (SYMBOL "="), (SYMBOL "b"), (SYMBOL ")"), (SYMBOL "="), (SYMBOL "c"), (END "$$$")]',
     "(= (= a b) c)")
]

