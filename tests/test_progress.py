import os
import tempfile
import unittest
import unittest.mock

import kurt.kurt as kurt


class TestProgress(unittest.TestCase):
    # `RunConfig(progress=...)`: which line of which file is checked (the playground's progress bar)

    def test_the_lines_of_each_file_in_order(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, 'dep.kurt'), 'w', encoding='utf-8') as stream:
                stream.write('prop P\n\nuse P "given"\n')
            events: list[dict] = []
            session = kurt.Session(kurt.RunConfig(paths=(tmp,), progress=events.append))
            result = session.check_text('load dep\nP\n', name='main.kurt')
            self.assertTrue(result.ok, result.error)
            seen = [(os.path.basename(e['file']), e['line'], e['lines'], e['files'], e['done']) for e in events]
            self.assertEqual([e['index'] for e in events], [1, 1, 2, 2, 2, 2, 1, 1])
            self.assertEqual(seen, [('main.kurt', 0, 2, 1, False), ('main.kurt', 1, 2, 1, False),
                                    ('dep.kurt', 0, 3, 2, False), ('dep.kurt', 1, 3, 2, False),   # (not the blank line 2)
                                    ('dep.kurt', 3, 3, 2, False), ('dep.kurt', 3, 3, 2, True),
                                    ('main.kurt', 2, 2, 2, False), ('main.kurt', 2, 2, 2, True)])
            # checked again, the theory comes from the cache: only the main file is checked
            events.clear()
            session.check_text('load dep\nP\n', name='main.kurt')
            self.assertEqual({os.path.basename(e['file']) for e in events}, {'main.kurt'})
            self.assertEqual(events[-1]['files'], 1)

    def test_without_progress_nothing_changes(self):
        text = 'load propositional\nprop A\nuse A\nA or A\n'
        self.assertEqual(kurt.Session(kurt.RunConfig(progress=lambda e: None)).check_text(text).output,
                         kurt.Session().check_text(text).output)

    def test_the_language_server_passes_it_on(self):
        events: list[dict] = []
        server = kurt.LanguageServer(None, None)
        server.progress = events.append
        uri = 'file:///tmp/progress.kurt'
        server.texts[uri] = 'prop A\nuse A\n'
        with unittest.mock.patch.object(server, 'publish_diagnostics', lambda *args: None):
            server.check(uri)
        self.assertEqual(events[-1], {'file': '/tmp/progress.kurt', 'line': 2, 'lines': 2, 'index': 1, 'files': 1, 'done': True})


if __name__ == '__main__':
    unittest.main()
