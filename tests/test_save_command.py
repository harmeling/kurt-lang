import copy
import os
import tempfile
import unittest

import kurt

# Regression test for the `save` keyword: flattens the current theory + syntax into
# self-contained `.kurt` source that reloads via `load`, without needing to re-derive
# anything (see save_state_str, and todo-claude.md's writeup). The interesting failure
# mode isn't "save crashes" -- it's "save's *output* doesn't actually reload cleanly",
# so this test always round-trips: save, then load the saved file into a fresh session
# and check the result is proof-checkable and mentions the original facts.

class TestSaveCommand(unittest.TestCase):
    def test_save_output_reloads_and_preserves_the_theory(self):
        with tempfile.TemporaryDirectory() as tmp:
            source_path = os.path.join(tmp, 'source.kurt')
            saved_path = os.path.join(tmp, 'saved.kurt')
            with open(source_path, 'w') as fh:
                fh.write(f'''load prop
bool A, B
use A implies B "mp"
use A

show B
proof
    B
qed

save "{saved_path}"
''')
            kb = copy.deepcopy(kurt.initial_kb)
            kurt.load_file(source_path, kb, mainstream=False)
            self.assertTrue(os.path.exists(saved_path), '`save` did not write its output file')

            reloaded_kb = copy.deepcopy(kurt.initial_kb)
            reloaded_kb = kurt.load_file(saved_path, reloaded_kb, mainstream=False)
            labels = {f.label for f in reloaded_kb.theory}
            self.assertIn('mp', labels, 'the saved file lost the labelled fact `mp`')
            # `B` was proven (keyword '') in the original session, with no label -- `save` must
            # still export it across the reload, which requires synthesizing a label for it
            # (an unlabelled fact is otherwise dropped by ordinary `load` selective-export
            # rules the moment the saved file is loaded from somewhere else, see
            # save_state_str's own comment on this)
            exprs = {kurt.expr_str(f.expr, reloaded_kb) for f in reloaded_kb.theory}
            self.assertIn('B', exprs, 'the saved file lost the proven fact `B`')

    def test_save_round_trips_operators_chains_and_function_application(self):
        # exercises the trickier cases together: `chain` (which immediately synthesizes and
        # `use`s formulas mentioning its operators, so `bool`/`infix` must be emitted before
        # `chain` in save's own output -- see save_state_str's ordering comment), and a bare
        # function application nested inside a tighter-binding infix operator (`f a ∈ B`,
        # which used to round-trip as `f (a ∈ B)` before expr_normal's missing-parens bug for
        # plain calls was fixed alongside this feature).
        with tempfile.TemporaryDirectory() as tmp:
            source_path = os.path.join(tmp, 'source.kurt')
            saved_path = os.path.join(tmp, 'saved.kurt')
            with open(source_path, 'w') as fh:
                fh.write(f'''load prop, equality, set
const f, g
var a
save "{saved_path}"
''')
            kb = copy.deepcopy(kurt.initial_kb)
            kurt.load_file(source_path, kb, mainstream=False)
            self.assertTrue(os.path.exists(saved_path))

            reloaded_kb = copy.deepcopy(kurt.initial_kb)
            reloaded_kb = kurt.load_file(saved_path, reloaded_kb, mainstream=False)   # must not raise
            labels = {f.label for f in reloaded_kb.theory}
            self.assertIn('function-extensionality', labels)

if __name__ == '__main__':
    unittest.main()
