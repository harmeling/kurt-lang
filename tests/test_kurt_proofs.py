import os
import re
import io
import copy
import unittest
import kurt
import pathlib
import contextlib
import importlib.resources as res

from tests.utils import PROJECT_ROOT
proofs_root = PROJECT_ROOT / "proofs"
theories_root = res.files("kurt.theories")

print("PROJECT_ROOT =", PROJECT_ROOT)
print("proofs_root =", proofs_root)
print("theories_root =", theories_root)

def traversable_rglob(root, pattern=".kurt"):
    """Recursively yield all files ending with pattern from a Traversable root."""
    for item in root.iterdir():
        if item.is_file() and str(item).endswith(pattern):
            yield item
        elif item.is_dir():
            yield from traversable_rglob(item, pattern)

def file_last_line(fname):
    # a file's last line can start with `;;; ` to assert a *specific* expected last line of
    # output -- needed for a file whose point is a precise error message (e.g. a rejection
    # that happens while *closing* a block, which `expect` can't wrap, see
    # forall-intro-rejects-leaked-constant.kurt) or specific non-error output text. Without
    # that marker, a file is simply expected to run to completion without raising -- whether
    # that's an ordinary successful proof, or a file that uses `expect` internally to check
    # its own interesting condition and finish cleanly either way. This used to be mandatory
    # (every file needed *some* marker, even the information-free `;;; Proof checked.` the
    # vast majority of files just repeated) -- relaxed since a missing marker is exactly as
    # informative as `;;; Proof checked.` was, and forcing every file to spell that out
    # bought nothing (see todo-claude.md).
    content = fname.read_text()
    lines = content.splitlines()
    last = lines[-1].strip() if lines else ''
    if last.startswith(';;; '):
        return last[4:]
    return 'Proof checked.'

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
        example_paths = sorted(proofs_root.rglob("*.kurt"))
        example_paths += list(traversable_rglob(theories_root, "*.kurt"))
        # Optional: make sure we actually found something to test
        self.assertTrue(example_paths, "No `.kurt` files found under proofs/")

        for i, path in enumerate(example_paths):
            with self.subTest(i=i, msg=path):
                kb = copy.deepcopy(kurt.initial_kb)
                true_last_line = file_last_line(path)
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
                if actual_last_line == true_last_line:
                    self.assertEqual(actual_last_line, true_last_line)
                else:
                    self.assertEqual(actual_last_line[:17], true_last_line[:17])

if __name__ == '__main__':
    unittest.main()