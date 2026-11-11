import io
import unittest

import kurt.kurt as kurt

PROOF = '''load logic
any x
prop P
arity P 1
use ∃ x (P x)
show ∃ x (P x)
proof
    pick a with P a
        P a
'''


class TestPickSource(unittest.TestCase):
    # the `pick` line names the `∃` line it picks from: in its message, its event, and its hover

    def test_the_message_and_the_event_name_the_existential(self):
        result = kurt.check_text(PROOF)
        event = next(e for e in result.events if e['text'].startswith('pick '))
        self.assertIn('new constant `a`, by 5', event['reason'])
        self.assertEqual(event['uses'], ['5'])

    def test_the_hover_links_the_existential(self):
        uri = 'file:///pick.kurt'
        server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
        server.texts[uri], server.versions[uri] = PROOF, 1
        server.check(uri)
        found = server.hover({'textDocument': {'uri': uri}, 'position': {'line': 7, 'character': 0}})
        value = found['contents']['value'] if found else ''
        self.assertIn('by 5', value)
        self.assertIn(f'[line 5]({uri}#L5)', value)


if __name__ == '__main__':
    unittest.main()
