import threading
import unittest

import kurt.kurt as kurt

# the run state is one object (`RunState`) that a session swaps in as a whole; sessions take turns
# under a lock, so several threads can use their own sessions (2026-10-09)

PROOF = 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n'
UNDECLARED = 'load prop\nuse A\nA\n'                       # an error only with `strict`
TEXTS = [PROOF, UNDECLARED, 'load numbers\ncalc on\n17 * 42 = 714\n', 'load logic\nbool P\narity P 1\nconst P\nuse ∀ x P(x)\nconst c\nP(c)\n']
CONFIGS = [kurt.RunConfig(), kurt.RunConfig(strict=True), kurt.RunConfig(comment_indent=30)]


def outcome(result):
    return result.ok, result.output, result.error, [{k: v for k, v in e.items() if k != 'line'} for e in result.events]


class TestSessionsAndThreads(unittest.TestCase):
    def expected(self):
        return {(i, j): outcome(kurt.new_session(config).check_text(text))
                for i, config in enumerate(CONFIGS) for j, text in enumerate(TEXTS)}

    def test_threads_give_the_results_of_one_after_the_other(self):
        expected = self.expected()
        results, errors = {}, []
        def work(i, config):
            try:
                session = kurt.new_session(config)
                for _ in range(2):
                    for j, text in enumerate(TEXTS):
                        results[(i, j)] = outcome(session.check_text(text))
            except Exception as e:       # (reported below, not lost in the thread)
                errors.append(e)
        threads = [threading.Thread(target=work, args=(i, config)) for i, config in enumerate(CONFIGS)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        self.assertEqual(errors, [])
        self.assertEqual(results, expected)

    def test_a_reused_session_agrees_with_fresh_ones(self):
        expected = self.expected()
        sessions = [kurt.new_session(config) for config in CONFIGS]
        for _ in range(2):
            for j, text in enumerate(TEXTS):
                for i, session in enumerate(sessions):          # alternating between the sessions
                    self.assertEqual(outcome(session.check_text(text)), expected[(i, j)])

    def test_a_session_leaves_the_run_state_alone(self):
        before = kurt.run_state
        kurt.new_session(kurt.RunConfig(strict=True)).check_text(PROOF)
        self.assertIs(kurt.run_state, before)
        self.assertFalse(kurt.run_state.strict_mode)

if __name__ == '__main__':
    unittest.main()
