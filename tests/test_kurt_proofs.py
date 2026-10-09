import io
import os
import copy
import unittest
import concurrent.futures
import kurt.kurt as kurt
import contextlib
import pathlib
import importlib.resources as res

from tests.utils import PROJECT_ROOT
proofs_root = PROJECT_ROOT / "proofs"
theories_root = res.files("kurt.theories")

# every `.kurt` file under `proofs/` and every theory must check: run to completion without an
# error. A file whose point is an error says so with `expect "KIND" "TEXT"` around it (the text
# is optional); an error that can only happen at the level of a whole file (a block still open at
# its end, `break` at its top level, a circular `load`, ...) is in a helper file, in a directory
# `helpers/`, which `expect` around a `load` checks -- the helper files aren't tests of their own.
# minimal.kurt isn't one either: it is the core, which Kurt reads when it starts, and can't be loaded

def traversable_rglob(root, pattern=".kurt"):
    """Recursively yield all files ending with pattern from a Traversable root."""
    for item in root.iterdir():
        if item.is_file() and str(item).endswith(pattern):
            yield item
        elif item.is_dir():
            yield from traversable_rglob(item, pattern)

def is_test_file(path) -> bool:
    return 'helpers' not in path.parts and path.name != 'minimal.kurt'

def check_file(path_str: str):
    # check one file (in a process of its own): `None`, or the last line of its error
    path = pathlib.Path(path_str)
    lines = path.read_text(encoding='utf-8').splitlines()
    if lines and lines[-1].startswith(';;; '):
        return 'no `;;; ` markers any more: use `expect "KIND" "TEXT"`'
    kb = copy.deepcopy(kurt.initial_kb)
    out_buf, err_buf = io.StringIO(), io.StringIO()
    try:
        # (the kernel checks every step, and a `KernelError` makes the test fail)
        with contextlib.redirect_stdout(out_buf), contextlib.redirect_stderr(err_buf):
            _ = kurt.load_file(str(path), kb, main=True)   # as when running the file, so the output is produced too
    except kurt.KurtException as e:
        return (err_buf.getvalue() or e.msg).strip().split('\n')[-1]
    return None

# the files are checked by `KURT_TEST_JOBS` processes at the same time (default 4: the login node is
# shared; 1 checks them one after the other in this process)
JOBS = int(os.environ.get('KURT_TEST_JOBS', '4'))

class TestProving(unittest.TestCase):
    def test_proving(self):
        example_paths = sorted(proofs_root.rglob("*.kurt"))
        example_paths += list(traversable_rglob(theories_root, ".kurt"))   # (`.kurt`, not `*.kurt`: a suffix, not a pattern)
        example_paths = [p for p in example_paths if is_test_file(p)]
        self.assertTrue(example_paths, "No `.kurt` files found under proofs/")
        names = [str(p) for p in example_paths]
        if JOBS > 1:
            with concurrent.futures.ProcessPoolExecutor(max_workers=JOBS) as pool:
                errors = list(pool.map(check_file, names, chunksize=1))
        else:
            errors = [check_file(n) for n in names]
        for i, (name, error) in enumerate(zip(names, errors)):
            with self.subTest(i=i, msg=name):
                self.assertIsNone(error)

if __name__ == '__main__':
    unittest.main()
