import os
import re
import io
import copy
import unittest
import kurt
import pathlib
import contextlib

def file_last_line(fname):
    # the last line in the file starts with `;;; ` and contains the expected last line of the output
    with open(fname, "r") as f:
        return f.readlines()[-1].strip()[4:]

def str_last_line(s):
    return s.strip().split('\n')[-1]

def normalize_path_in_line(line: str) -> str:
    # Match typical filesystem paths (Windows or Unix)
    path_pattern = r"([A-Za-z]:)?[\\/][\w .\\/-]+"

    def normalize_match(match):
        path = match.group(0)
        return os.path.normpath(path)

    # Normalize all path-like substrings
    normalized_line = re.sub(path_pattern, normalize_match, line)
    return normalized_line

class TestProving(unittest.TestCase):
    def test_proving(self):
        example_paths = sorted(pathlib.Path("proofs").rglob("*.kurt"))
        # Optional: make sure we actually found something to test
        self.assertTrue(example_paths, "No .kurt files found under proofs/")

        for i, path in enumerate(example_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                true_last_line = file_last_line(str(path))
                out_buf, err_buf = io.StringIO(), io.StringIO()
                try:
                    with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
                        _ = kurt.load_file(str(path), kb, mainstream=False)
                        print("Proof checked.")
                    actual_last_line = str_last_line(out_buf.getvalue())

                except kurt.KurtException as e:
                    # stderr was redirected in the with-block, so use what was captured.
                    actual_last_line = str_last_line(err_buf.getvalue() or e.msg)

                # Normalize paths in both lines before comparison
                actual_last_line = normalize_path_in_line(actual_last_line)
                true_last_line = normalize_path_in_line(true_last_line)
                self.assertEqual(actual_last_line, true_last_line)

if __name__ == '__main__':
    unittest.main()