import contextlib
import copy
import io
import os
import tempfile
import unittest

import kurt.kurt as kurt

# each loaded file is checked in a fresh context: the core and what it loads itself, nothing
# of the file that loads it (dev/codex-suggestions.md, 2026-09-29) -- so a library can't depend on
# its loader's facts without loading them, and the order of loads doesn't matter


class LoadTestCase(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()

    def tearDown(self):
        self.dir.cleanup()

    def write(self, name: str, text: str) -> str:
        path = os.path.join(self.dir.name, name)
        with open(path, 'w') as fh:
            fh.write(text)
        return path

    def check(self, name: str) -> tuple[kurt.KnowledgeBase, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            kb = kurt.load_file(os.path.join(self.dir.name, name), copy.deepcopy(kurt.initial_kb), main=True)
        return kb, out.getvalue()

    def fails(self, name: str) -> str:
        with self.assertRaises(kurt.KurtException) as e:
            self.check(name)
        return e.exception.msg


class TestIsolation(LoadTestCase):
    def test_a_library_can_not_use_facts_of_its_loader(self):
        self.write('facts.kurt', 'bool A, B\nuse A "a"\nuse A implies B "ab"\n')
        self.write('lib.kurt', 'bool A, B\nB "b"\n')                 # needs `facts`, doesn't load it
        self.write('main.kurt', 'load facts\nload lib\n')
        self.assertIn('can not derive `B`', self.fails('main.kurt'))
        self.write('lib.kurt', 'load facts\nB "b"\n')                 # now it does
        kb, _ = self.check('main.kurt')
        self.assertIn('b', {f.label for f in kb.theory})

    def test_the_order_of_loads_does_not_matter(self):
        self.write('x.kurt', 'bool A\nuse A "a"\n')
        self.write('y.kurt', 'bool B\nuse B "b"\n')
        self.write('xy.kurt', 'load x\nload y\n')
        self.write('yx.kurt', 'load y\nload x\n')
        labels = [sorted(f.label for f in self.check(name)[0].theory) for name in ('xy.kurt', 'yx.kurt')]
        self.assertEqual(labels[0], labels[1])

    def test_a_library_sees_only_what_it_loads(self):
        seen = []
        self.write('big.kurt', ''.join(f'bool A{i}\nuse A{i} "a{i}"\n' for i in range(50)))
        self.write('lib.kurt', 'bool C\nuse C "c"\ntheory\n')
        self.write('main.kurt', 'load big\nload lib\n')
        read_eval_loop = kurt.read_eval_loop
        def recording(f, kb):
            kb = read_eval_loop(f, kb)
            if f.name.endswith('lib.kurt'):
                seen.append(sum(len(node.theory) for node in kb.levels()))
            return kb
        kurt.read_eval_loop = recording
        try:
            self.check('main.kurt')
        finally:
            kurt.read_eval_loop = read_eval_loop
        self.assertEqual(seen, [1])

    def test_a_diamond_gives_each_fact_once(self):
        self.write('base.kurt', 'bool A\nuse A "a"\n')
        self.write('left.kurt', 'load base\nbool L\nuse L "l"\n')
        self.write('right.kurt', 'load base\nbool R\nuse R "r"\n')
        self.write('main.kurt', 'load left, right\nA\n')
        kb, _ = self.check('main.kurt')
        self.assertEqual([f.label for f in kb.theory].count('a'), 1)

    def test_todos_of_a_library_count(self):
        self.write('lib.kurt', 'bool A\ntodo A "a"\n')
        self.write('main.kurt', 'load lib\nA\n')
        kb, _ = self.check('main.kurt')
        self.assertEqual(len(kb.todos()), 1)


class TestConflicts(LoadTestCase):
    def test_a_def_is_only_for_a_new_symbol(self):
        # `f` is a constant with a fact here, and defined in the library: `f = 1`, `f = 2`
        self.write('lib.kurt', 'load equality\ndef f = 2 "f-def"\n')
        self.write('main.kurt', 'load equality\nconst f\nuse f = 1 "f-one"\nload lib\n')
        self.assertIn('is defined in', self.fails('main.kurt'))
        self.write('main.kurt', 'load lib\nconst g\n')                  # fine alone
        self.check('main.kurt')

    def test_the_same_def_from_both_sides_is_fine(self):
        self.write('d.kurt', 'load equality\ndef f = 2 "f-def"\n')
        self.write('lib.kurt', 'load d\nf = 2 "f-two"\n')
        self.write('main.kurt', 'load d\nload lib\nf = 2\n')
        self.check('main.kurt')

    def test_declarations_must_agree(self):
        self.write('lib.kurt', 'bool P 0 1\nuse P (A and B) "p"\n')
        self.write('main.kurt', 'bool P\nuse P "q"\nload lib\n')
        self.assertIn('declared differently', self.fails('main.kurt'))

    def test_a_symbol_is_declared_by_one_file_only(self):
        # the same declaration from two files is an error too (numbers.kurt and field.kurt both
        # declare `+`, with laws for different things), in both orders, directly or via a `load`
        self.write('lib.kurt', 'bool P\narity P 2\nuse P $x $y "p"\n')
        self.write('main.kurt', 'bool P\narity P 2\nuse P $x $x "q"\nload lib\n')
        self.assertIn('declared by one file only', self.fails('main.kurt'))
        self.write('ops.kurt', 'load equality\ninfix ∘ 50 50\nuse $a ∘ $b = $b ∘ $a "comm"\n')
        self.write('other.kurt', 'load equality\ninfix ∘ 50 50\nuse $a ∘ $a = $a "idem"\n')
        self.write('both.kurt', 'load ops\nload other\n')
        self.assertIn('declared in `ops.kurt` and in `other.kurt`', self.fails('both.kurt'))
        self.write('via.kurt', 'load other\n')
        self.write('both2.kurt', 'load via\nload ops\n')
        self.assertIn('declared in `other.kurt` and in `ops.kurt`', self.fails('both2.kurt'))

    def test_the_same_file_twice_is_fine(self):
        # a diamond: two files load the same theory, a third loads both
        self.write('ops.kurt', 'load equality\ninfix ∘ 50 50\nuse $a ∘ $b = $b ∘ $a "comm"\n')
        self.write('left.kurt', 'load ops\nconst a\na ∘ a = a ∘ a "l"\n')
        self.write('right.kurt', 'load ops\nconst b\nb ∘ b = b ∘ b "r"\n')
        self.write('main.kurt', 'load left\nload right\na ∘ b = b ∘ a\n')
        self.check('main.kurt')


class TestCache(LoadTestCase):
    def test_a_changed_dependency_is_checked_again(self):
        self.write('base.kurt', 'bool A\nuse A "a"\n')
        self.write('lib.kurt', 'load base\nA "a2"\n')
        self.write('main.kurt', 'load lib\n')
        self.check('main.kurt')
        self.write('base.kurt', 'bool A\n')                            # `A` doesn't hold anymore
        self.assertIn('can not derive `A`', self.fails('main.kurt'))

    def test_a_library_is_checked_once(self):
        self.write('lib.kurt', 'load natural\n0 ∈ Nat "zero"\n')
        self.write('main.kurt', 'load lib\n')
        reads = []
        read_eval_loop = kurt.read_eval_loop
        def counting(f, kb):
            reads.append(os.path.basename(f.name))
            return read_eval_loop(f, kb)
        kurt.read_eval_loop = counting
        try:
            self.check('main.kurt')
            self.check('main.kurt')
        finally:
            kurt.read_eval_loop = read_eval_loop
        self.assertEqual(reads.count('lib.kurt'), 1)
        self.assertEqual(reads.count('main.kurt'), 2)           # the main file prints its steps: always

if __name__ == '__main__':
    unittest.main()
