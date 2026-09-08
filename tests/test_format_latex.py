import os
import copy
import io
import contextlib
import tempfile
import unittest

import kurt

class TestFormatLatexAppliesSymbolMapping(unittest.TestCase):
    def test_declared_latex_replacement_is_used(self):
        # `format latex` used to be unreachable from a `.kurt` file at all (see
        # proofs/soundness/format-latex-argument-parses.kurt). Once made reachable, it exposed
        # a further, pre-existing bug: `expr_latex` was a stale copy of `expr_normal` that
        # still called `expr_normal` recursively and never consulted `kb.get_latex` -- so
        # `format latex` silently printed exactly the same thing as `format normal`, ignoring
        # any `latex SYMBOL REPLACEMENT` declaration. This test needs `mainstream=True`
        # (real printed output), which the auto-discovered `proofs/` harness never exercises
        # (it always calls `load_file` with `mainstream=False`) -- so it has to live here.
        source = 'bool A, B\ninfix "+" 20 20\nlatex "+" "\\oplus"\nformat latex\nuse A + B "demo"\n'
        with tempfile.NamedTemporaryFile(mode='w', suffix='.kurt', delete=False) as f:
            f.write(source)
            path = f.name
        try:
            kb = copy.deepcopy(kurt.initial_kb)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                kurt.load_file(path, kb, mainstream=True)
            printed = out.getvalue()
            self.assertIn(r'\oplus', printed)
            self.assertNotIn('A + B', printed)
        finally:
            os.unlink(path)

if __name__ == '__main__':
    unittest.main()
