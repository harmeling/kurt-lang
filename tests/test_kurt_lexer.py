import unittest
import kurt
from examples import examples

class Test_Lexing(unittest.TestCase):
    def test_lexing(self):
        for i in range(len(examples)):
            (input_line, true_output, _) = examples[i]  # pick input, lexed
            try:
                output = str(list(kurt.scan_string(input_line)))  # peekable token stream
            except Exception as e:
                output = (str(e).split('\n'))[-1]    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

if __name__ == '__main__':
    unittest.main()