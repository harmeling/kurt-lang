import kurt
import unittest

## test code for lexing and parsing
# three entries: input, scanned, parsed
test_examples = [
    # left associative
    ("1 - 1 + 1",
     '[(INT "1"), (SYMBOL "-"), (INT "1"), (SYMBOL "+"), (INT "1"), (END "")]',
     "(+ (- 1 1) 1)"),
    # left associative
    ("(1 - 1) + 1",
     '[(SYMBOL "("), (INT "1"), (SYMBOL "-"), (INT "1"), (SYMBOL ")"), (SYMBOL "+"), (INT "1"), (END "")]',
     "(+ (- 1 1) 1)"),
    # right associative
    ("1 - (1 + 1)",
     '[(INT "1"), (SYMBOL "-"), (SYMBOL "("), (INT "1"), (SYMBOL "+"), (INT "1"), (SYMBOL ")"), (END "")]',
     "(- 1 (+ 1 1))"),
    # left associative
    ("12 / 3 / 4",
     '[(INT "12"), (SYMBOL "/"), (INT "3"), (SYMBOL "/"), (INT "4"), (END "")]',
     "(/ (/ 12 3) 4)"),
    # simple sum
    ("17 + 42",
     '[(INT "17"), (SYMBOL "+"), (INT "42"), (END "")]',
     "(+ 17 42)"),
    # simple sum with flatness
    ("17 + 42 + 100",
     '[(INT "17"), (SYMBOL "+"), (INT "42"), (SYMBOL "+"), (INT "100"), (END "")]',
     "(+ (+ 17 42) 100)"),
    # unary minus
    ("-1",
     '[(SYMBOL "-"), (INT "1"), (END "")]',
     "(- 1)"),
    # function call
    ("x (-1)",
     '[(SYMBOL "x"), (SYMBOL "("), (SYMBOL "-"), (INT "1"), (SYMBOL ")"), (END "")]',
     "(x (- 1))"),
    # assign
    ("x = 1",
     '[(SYMBOL "x"), (SYMBOL "="), (INT "1"), (END "")]',
     "(= x 1)"),
    # assign with unary minus
    ("x = -1",
     '[(SYMBOL "x"), (SYMBOL "="), (SYMBOL "-"), (INT "1"), (END "")]',
     "(= x (- 1))"),
    # unary minus in sum with flatness
    ("-1 + 18 + -15",
     '[(SYMBOL "-"), (INT "1"), (SYMBOL "+"), (INT "18"), (SYMBOL "+"), (SYMBOL "-"), (INT "15"), (END "")]',
     "(+ (+ (- 1) 18) (- 15))"),    
    # unary minus in product
    ("3 * -5",
     '[(INT "3"), (SYMBOL "*"), (SYMBOL "-"), (INT "5"), (END "")]',
     "(* 3 (- 5))"),
    # "*-" is unknown operator
    ("3 *- 5",
     '[(INT "3"), (SYMBOL "*-"), (INT "5"), (END "")]',
     "(3 *- 5)"),
    # simple postfix
    ("17!",
     '[(INT "17"), (SYMBOL "!"), (END "")]',
     "(! 17)"),
    # function call
    ("f 18",
     '[(SYMBOL "f"), (INT "18"), (END "")]',
     "(f 18)"),
    # function call binds less than most other stuff
    ("f 18 + 42",
     '[(SYMBOL "f"), (INT "18"), (SYMBOL "+"), (INT "42"), (END "")]',
     "(f (+ 18 42))"),
    # function call is left associative
    ("f 178 42",
     '[(SYMBOL "f"), (INT "178"), (INT "42"), (END "")]',
     "(f 178 42)"),
    # function call with sum
    ("f 178 + 432 422",
     '[(SYMBOL "f"), (INT "178"), (SYMBOL "+"), (INT "432"), (INT "422"), (END "")]',
     "(f (+ 178 432) 422)"),
    # two function calls
    ("f (2) (3)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "2"), (SYMBOL ")"), (SYMBOL "("), (INT "3"), (SYMBOL ")"), (END "")]',
     "(f 2 3)"),
    # product before sum
    ("a + b * c",
     '[(SYMBOL "a"), (SYMBOL "+"), (SYMBOL "b"), (SYMBOL "*"), (SYMBOL "c"), (END "")]',
     "(+ a (* b c))"),
    # product before sum
    ("a * b + c",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "b"), (SYMBOL "+"), (SYMBOL "c"), (END "")]',
     "(+ (* a b) c)"),
    # sum before product with brackets
    ("a * (b + c)",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "("), (SYMBOL "b"), (SYMBOL "+"), (SYMBOL "c"), (SYMBOL ")"), (END "")]',
     "(* a (+ b c))"),
    # 
    ("f3 1 2 3",
     '[(SYMBOL "f3"), (INT "1"), (INT "2"), (INT "3"), (END "")]',
     "(f3 1 2 3)"),
    # 
    ("f3 1 2+4 3",
     '[(SYMBOL "f3"), (INT "1"), (INT "2"), (SYMBOL "+"), (INT "4"), (INT "3"), (END "")]',
     "(f3 1 (+ 2 4) 3)"),
    # one function call
    ("f (17)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "17"), (SYMBOL ")"), (END "")]',
     "(f 17)"),
    # one function call
    ("f (17, 42)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "17"), (SYMBOL ","), (INT "42"), (SYMBOL ")"), (END "")]',
     "(f (, 17 42))"),
    # one function call
    ("f 17",
     '[(SYMBOL "f"), (INT "17"), (END "")]',
     "(f 17)"),
    # one function call
    ("f 17 42",
     '[(SYMBOL "f"), (INT "17"), (INT "42"), (END "")]',
     "(f 17 42)"),
    # one function call
    ("f (17, 42)",
     '[(SYMBOL "f"), (SYMBOL "("), (INT "17"), (SYMBOL ","), (INT "42"), (SYMBOL ")"), (END "")]',
     "(f (, 17 42))"),
    # one function call
    ("f(a, b)",
     '[(SYMBOL "f"), (SYMBOL "("), (SYMBOL "a"), (SYMBOL ","), (SYMBOL "b"), (SYMBOL ")"), (END "")]',
     "(f (, a b))"),
    # 
    ("assume x in y",
     '[(SYMBOL "assume"), (SYMBOL "x"), (SYMBOL "in"), (SYMBOL "y"), (END "")]',
     "(assume x in y)"),
    # 
    ("1 key1 2+3 key2",
     '[(INT "1"), (SYMBOL "key1"), (INT "2"), (SYMBOL "+"), (INT "3"), (SYMBOL "key2"), (END "")]',
     "(1 key1 (+ 2 3) key2)"),
    # sum of two bracket expressions
    ("(a b) + (c d)",
     '[(SYMBOL "("), (SYMBOL "a"), (SYMBOL "b"), (SYMBOL ")"), (SYMBOL "+"), (SYMBOL "("), (SYMBOL "c"), (SYMBOL "d"), (SYMBOL ")"), (END "")]',
     "(+ (a b) (c d))"),
    # space binds stronger than comma
    ("a, b c, d",
     '[(SYMBOL "a"), (SYMBOL ","), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL ","), (SYMBOL "d"), (END "")]',
     "(, (, a (b c)) d)"),
    # two expressions
    ("a * b c + d",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL "+"), (SYMBOL "d"), (END "")]',
     "((* a b) (+ c d))"),
    # equality vs space
    ("a = b c d = e)",
     '[(SYMBOL "a"), (SYMBOL "="), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL "d"), (SYMBOL "="), (SYMBOL "e"), (SYMBOL ")"), (END "")]',
     "(= (= a (b c d)) e)"),
    # this should not work
    ("a +",
     '[(SYMBOL "a"), (SYMBOL "+"), (END "")]',
     "SyntaxError: expression expected, got end of line"),
    # this should not work
    ("a * b c +",
     '[(SYMBOL "a"), (SYMBOL "*"), (SYMBOL "b"), (SYMBOL "c"), (SYMBOL "+"), (END "")]',
     "SyntaxError: expression expected, got end of line"),
    # this should not work
    ("a b +",
     '[(SYMBOL "a"), (SYMBOL "b"), (SYMBOL "+"), (END "")]',
     "SyntaxError: expression expected, got end of line")
]

class Test_Lexing(unittest.TestCase):
    def test_lexing(self):
        #print('Running tests.')
        n = len(test_examples)
        passed = 0
        for i in range(n):
            (input_line, true_output, _) = test_examples[i]  # pick input, lexed
            try:
                output = str(list(kurt.scan_string(input_line)))  # peekable token stream
            except Exception as e:
                output = (str(e).split('\n'))[-1]    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

class Test_Parsing(unittest.TestCase):
    def test_parsing(self):
        #print('Running tests.')
        kurt.load_file('standards.kurt', kurt.initial_kb)
        kurt.initial_kb.format = 'sexpr'
        n = len(test_examples)
        passed = 0
        for i in range(n):
            (input_line, _, true_output) = test_examples[i]    # pick input, parsed
            try:
                ts = kurt.PG(kurt.scan_string(input_line))     # peekable token stream
                pt = kurt.parse_tokenstream(ts, kurt.initial_kb)[0]  # parse tree
                output = kurt.expr_str(pt, kurt.initial_kb)
            except Exception as e:
                output = (str(e).split('\n'))[-1]    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

if __name__ == '__main__':
    unittest.main()