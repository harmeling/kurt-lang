import os
import subprocess
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

# scripts/publish-public.sh replaces everything in the public checkout: it must refuse anything
# that isn't a clean checkout of the public repository on main (dev/astra-suggestions.md, 9)

SCRIPT = PROJECT_ROOT / 'scripts' / 'publish-public.sh'


@unittest.skipUnless(SCRIPT.exists(), 'the publish script stays in the private repository')
class TestPublishScript(unittest.TestCase):
    def git(self, cwd, *args):
        subprocess.run(['git', *args], cwd=cwd, check=True, capture_output=True)

    def checkout(self, parent, origin='git@github.com:harmeling/kurt-lang.git', branch='main'):
        path = os.path.join(parent, 'public')
        os.mkdir(path)
        self.git(path, 'init', '-q', '-b', branch)
        self.git(path, 'remote', 'add', 'origin', origin)
        with open(os.path.join(path, 'README.md'), 'w') as f:
            f.write('public\n')
        with open(os.path.join(path, '.gitignore'), 'w') as f:
            f.write('*.cache\n')
        self.git(path, 'add', '-A')
        self.git(path, '-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q', '-m', 'first')
        return path

    def publish(self, public):
        return subprocess.run(['bash', str(SCRIPT), public], cwd=str(PROJECT_ROOT), capture_output=True,
                              text=True, env=dict(os.environ, CHECK_ONLY='1'))

    def test_a_clean_public_checkout(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = self.publish(self.checkout(tmp))
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            self.assertIn('can take Kurt', run.stdout)

    def test_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            for case, make, reason in [
                    ('this repository', lambda: str(PROJECT_ROOT), 'inside this repository'),
                    ('another origin', lambda: self.checkout(tmp, origin='git@github.com:harmeling/kurt-lang-dev.git'), 'the origin'),
                    ('another branch', lambda: self.checkout(tmp, branch='agent'), 'not on main'),
                    ('not the top', lambda: os.path.join(self.checkout(tmp), 'sub'), 'not the top'),
                    ('untracked', lambda: self.checkout(tmp), 'untracked'),
                    ('ignored', lambda: self.checkout(tmp), 'ignored')]:
                with self.subTest(case=case):
                    public = make()
                    if case == 'not the top':
                        os.makedirs(os.path.join(public, '.git'))
                    if case == 'untracked':
                        with open(os.path.join(public, 'notes.txt'), 'w') as f:
                            f.write('mine\n')
                    if case == 'ignored':
                        with open(os.path.join(public, 'build.cache'), 'w') as f:
                            f.write('mine\n')
                    run = self.publish(public)
                    self.assertNotEqual(run.returncode, 0, run.stdout)
                    if case == 'untracked':
                        self.assertTrue(os.path.exists(os.path.join(public, 'notes.txt')))
                    if case == 'ignored':
                        self.assertTrue(os.path.exists(os.path.join(public, 'build.cache')))
                    self.assertIn(reason, run.stdout)
                    subprocess.run(['rm', '-rf', os.path.join(tmp, 'public')])

if __name__ == '__main__':
    unittest.main()
