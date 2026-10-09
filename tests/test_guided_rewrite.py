import contextlib
import copy
import io
import os
import tempfile
import unittest

import kurt.kurt as kurt

# the shortcut for rewriting steps (`guided_rewrite`): the rules it guides, the subterms where a
# goal differs from a fact, and that a chain of rewriting steps is still found with it


def kb_after(text: str) -> 'kurt.KnowledgeBase':
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'f.kurt')
        with open(path, 'w', encoding='utf-8') as f:
            f.write(text)
        kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kurt.load_file(path, kb, main=False)
        return kb


class TestGuidedRewrite(unittest.TestCase):
    def test_rewriting_rules(self):
        kb = kb_after('load equality, prop\n')
        labels = {f.label for f in kb.all_theory() if kurt.rewriting_variable(f, kb) is not None}
        self.assertIn('equal-elim', labels)
        self.assertIn('iff-subst', labels)
        self.assertNotIn('and-elim', labels)

    def test_differing_subterms(self):
        kb = kb_after('load numbers\n')
        parse = lambda t: kurt.post_process(kb, kurt.parse_expression(kurt.PeekableGenerator(kurt.scan_string(t, kb)), kb, kurt.begin_rbp))[0]
        found = [kurt.expr_str(e, kb) for e in kurt.differing_subterms(parse('x = a * (b + c)'), parse('x = a * (b + d)'), kb)]
        self.assertEqual(found[0], 'd')               # the smallest difference first
        self.assertIn('x = (a * (b + d))', found)      # and the parts around it

    def test_chain(self):
        hits = []
        original = kurt.guided_rewrite
        def counting(*args, **kwargs):
            found = original(*args, **kwargs)
            hits.append(found is not None)
            return found
        kurt.guided_rewrite = counting
        try:
            kb_after('load numbers\nconst a, b, c\nuse b = c\na * (b + 1) = a * (c + 1)\nuse c = 7\na * (b + 1) = a * (7 + 1)\n')
        finally:
            kurt.guided_rewrite = original
        self.assertTrue(any(hits))      # the step was found by the shortcut

if __name__ == '__main__':
    unittest.main()
