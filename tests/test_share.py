import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# `kurt --share FILE` and `kurt --unshare LINK`: a proof as the link of the playground (kurt-web's `#proof=`:
# the UTF-8 bytes in base64 with `-` and `_`, no padding) and back


def run(*args: str) -> subprocess.CompletedProcess:
    env = dict(os.environ, PYTHONPATH=os.path.join(PROJECT_ROOT, 'src'))
    return subprocess.run([sys.executable, '-m', 'kurt', *args], capture_output=True, text=True, encoding='utf-8', env=env)


class TestShare(unittest.TestCase):
    def test_the_code_of_the_playground(self):
        # what the playground's `encodeShare` makes of `true\n` (btoa gives `dHJ1ZQo=`)
        self.assertEqual(kurt.share_link('true\n'), 'https://www.kurt-lang.org/#proof=dHJ1ZQo')

    def test_the_url_safe_alphabet(self):
        text = '∀ x ∈ Nat (x ≥ 0)\n??>>~~\n'
        link = kurt.share_link(text)
        self.assertNotIn('+', link)
        self.assertNotIn('/', link.split('#', 1)[1])
        self.assertNotIn('=', link.split('#proof=')[1])
        self.assertEqual(kurt.unshare_text(link), (text, None))

    def test_a_link_with_a_folder_the_bare_code_and_padding(self):
        text = 'load logic\nuse A\n'
        code = kurt.share_link(text).split('#proof=')[1]
        self.assertEqual(kurt.unshare_text(f'https://x.org/#proof={code}&folder=tutorial/'), (text, 'tutorial/'))
        self.assertEqual(kurt.unshare_text(code), (text, None))
        self.assertEqual(kurt.unshare_text(code + '=' * (-len(code) % 4)), (text, None))

    def test_links_that_are_no_proof(self):
        with self.assertRaisesRegex(ValueError, 'names the file'):
            kurt.unshare_text('https://www.kurt-lang.org/#file=tutorial/02-prove-an-implication.kurt')
        with self.assertRaisesRegex(ValueError, 'no `#proof=`'):
            kurt.unshare_text('https://www.kurt-lang.org/#')
        with self.assertRaisesRegex(ValueError, 'not base64'):
            kurt.unshare_text('#proof=!!!')

    def test_the_command_line(self):
        text = 'prop A, B\nuse A implies B\nuse A\nB\n'
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(text)
            shared = run('--share', path)
            self.assertEqual(shared.returncode, 0)
            link = shared.stdout.strip()
            self.assertTrue(link.startswith('https://www.kurt-lang.org/#proof='))
            back = run('--unshare', link)
            self.assertEqual((back.returncode, back.stdout), (0, text))
            self.assertEqual(run('--unshare', link + '&folder=tutorial/').stderr.count('tutorial/'), 1)
            self.assertNotEqual(run('--unshare', '#file=x.kurt').returncode, 0)
            self.assertNotEqual(run('--share', os.path.join(tmp, 'none.kurt')).returncode, 0)
            self.assertFalse(os.path.exists(path + 'c'))        # (nothing is checked, no certificates)


if __name__ == '__main__':
    unittest.main()
