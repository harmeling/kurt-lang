import copy
import dataclasses
import io
import os
import tempfile
import unittest

import kurt.kurt as kurt
from tests.test_kernel import run_with_certificates

# `def` inside a block (todo 77, doc/kurt-spec.md §6.6 and §7.2, doc/kurt-soundness.md §8.51): the
# symbol and its fact belong to the level of the block, the block's result must not mention it --
# also for the kernel, which checks the closing of the block again; allowed with `--strict` and in
# a loaded file, where it is not exported; the hover, the documents and the foundations say so

LET_WITH_DEF = 'load logic\nprop P\narity P 1\nconst P\nlet x\n    def k iff P x\n    true\ntrue\n'


class TestKernel(unittest.TestCase):
    def test_the_kernel_rejects_a_defined_symbol_in_the_result(self):
        # `let x` / `def k iff P x` with the `def` as the last line would give `∀ x (k iff P x)`: the
        # search refuses it (proofs/soundness/def-in-a-block-escapes.kurt), and the kernel on its own
        # too -- `k` is a statement (a "vocabulary symbol"), which the old check let through
        verdicts = []
        verify = kurt.kernel_verify
        def recording(cert, kb):
            if cert.kind == 'forall-intro' and not verdicts:
                block = cert.block
                definition = next(f for f in block.theory if f.def_symbol == 'k')
                block.theory.append(definition)         # (the `def` as the last line)
                try:
                    goal = [cert.goal[0], cert.goal[1], definition.expr]
                    verdicts.append(verify(dataclasses.replace(cert, rule=definition, goal=goal), kb))
                finally:
                    block.theory.pop()
            return verify(cert, kb)
        kurt.kernel_verify = recording
        try:
            run_with_certificates(LET_WITH_DEF)
        finally:
            kurt.kernel_verify = verify
        self.assertTrue(verdicts, 'no `forall-intro` step')
        self.assertIsNotNone(verdicts[0], 'the defined `k` escapes the `let` block')
        self.assertIn("['k']", verdicts[0])

    def test_the_steps_with_a_def_in_a_block_have_certificates(self):
        certs = run_with_certificates('load logic\nprop P\narity P 1\nconst P, c\nuse P c\n'
                                      'show ∃ y P y\nproof\n    def m = c\n    P m\n    ∃ y P y\nqed\n')
        self.assertIn('forall-intro', [c.kind for c in run_with_certificates(LET_WITH_DEF)])
        # `P m` by "equal-elim" with the fact `m = c` of the block (a `def`, the kernel finds it in the block)
        self.assertTrue(any(f.def_symbol == 'm' for c in certs if c.kind == 'rule' for f in [c.rule, *c.facts] if f is not None))


class TestScope(unittest.TestCase):
    def check(self, text: str, strict: bool = False) -> kurt.CheckResult:
        return kurt.Session(kurt.RunConfig(strict=strict)).check_text(text, 'proof.kurt', certificates=True)

    def test_a_def_in_a_block_with_strict(self):
        # conservative by its form: allowed with `--strict` (for grading); `use` is not
        text = 'load logic\nprop P\narity P 1\nconst c\nshow P c ⇒ P c\nproof\n    assume P c\n        def k iff P c\n        k\n        P c\nqed\n'
        result = self.check(text, strict=True)
        self.assertTrue(result.ok, result.error)
        refused = self.check(text.replace('def k iff P c\n        k\n', 'use P c\n'), strict=True)
        self.assertFalse(refused.ok)
        self.assertIn('`use` is not allowed inside `assume`', refused.error or '')

    def test_the_symbol_is_gone_after_the_block(self):
        # the `kb` after the file: `t` is no constant of the top level, and its fact is gone
        result = self.check('load number\ncalc on\nshow ∃ x (x = 3)\nproof\n    def t = 3\n    t = 3\n    ∃ x (x = 3)\nqed\n')
        self.assertTrue(result.ok, result.error)
        kb = result._kb
        assert kb is not None
        self.assertFalse(kb.is_const('t'))
        self.assertFalse(kb.is_used('t'))
        self.assertFalse(any(f.def_symbol == 't' for f in kb.all_theory()))

    def test_a_loaded_file_with_a_def_in_a_block(self):
        # a theory may have one too (in the proof of a theorem): nothing of it is exported, the
        # loading file may define the same name itself
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, 'helper.kurt'), 'w', encoding='utf-8') as fh:
                fh.write('load logic\nprop P\narity P 1\nconst c\nuse P c "pc"\n'
                         'show ∃ y P y "some"\nproof\n    def m = c\n    P m\n    ∃ y P y\nqed\n')
            path = os.path.join(tmp, 'main.kurt')
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write('load "helper.kurt"\n∃ y P y\ndef m = c\nP m\n')
            result = kurt.Session().check_file(path)
            self.assertTrue(result.ok, result.error)

    def test_nothing_of_a_block_reaches_the_exports(self):
        kb = copy.deepcopy(kurt.initial_kb)
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'e.kurt')
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write('load logic\nprop P\narity P 1\nconst c\nuse P c "pc"\n'
                         'show ∃ y P y "some"\nproof\n    def m = c "m-def"\n    P m\n    ∃ y P y\nqed\n')
            with kurt.quietly():
                kb = kurt.load_file(path, kb)
        self.assertFalse(kb.is_known('m'))
        self.assertFalse(any(f.label == 'm-def' for f in kb.all_theory()))


class TestOutputs(unittest.TestCase):
    TEXT = ('load number\ncalc on\nshow ∃ x (x * x = 9)\nproof\n    def t = 3\n    t * t = 3 * 3\n'
            '    t * t = 9\n    ∃ x (x * x = 9)\nqed\n')

    def test_printed_as_a_top_level_def_indented_as_its_block(self):
        result = kurt.Session().check_text(self.TEXT)
        self.assertTrue(result.ok, result.error)
        self.assertIn('    def t = 3                             ; defining `t`', result.output)
        self.assertIn('    real t                                ; sort of its definition', result.output)
        events = [e for e in result.events if e['text'] == 'def t = 3']
        self.assertEqual([e['level'] for e in events], [1])

    def test_foundation(self):
        # the theorem rests on the definition (conservative); a line inside a block is no fact of its own
        result = kurt.Session().check_text(self.TEXT, foundation=True)
        entry = result.foundation('3')
        assert entry is not None
        self.assertEqual(entry['class'], 'theorem')
        self.assertIn('def', [p['kind'] for p in entry['rests_on']])

    def test_documents(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'proof.kurt')
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(self.TEXT)
            latex = kurt.export_document(path, 'latex', kurt.RunConfig())
            self.assertIn(r'\textbf{def} \; t = 3', latex)
            markdown = kurt.export_document(path, 'markdown', kurt.RunConfig())
            self.assertIn('defining `t`', markdown)
            text, missing = kurt.export_lean(path)
            self.assertIn('obtain ⟨t, ', text)            # a local constant with its equation (a Lean `obtain`)
            self.assertNotIn('axiom f', text.split('-- line 3')[1] if '-- line 3' in text else '')
            self.assertFalse([m for m in missing if 'def' in m], missing)

    def test_hover(self):
        with tempfile.TemporaryDirectory() as tmp:
            uri = 'file://' + os.path.join(tmp, 'h.kurt')
            server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
            server.texts[uri], server.versions[uri] = 'load number\ndef s = 2\n' + self.TEXT.split('\n', 1)[1], 1
            server.check(uri)
            def hover(line):
                found = server.hover({'textDocument': {'uri': uri}, 'position': {'line': line, 'character': 0}})
                return found['contents']['value'] if found else ''
            self.assertIn('**definition:**', hover(1))                         # at the top level: as before
            self.assertIn('**definition, local to its block:**', hover(5))     # `def t = 3` in the proof


if __name__ == '__main__':
    unittest.main()
