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

    def test_a_public_worktree(self):
        # a worktree is a checkout too, its `.git` a file (as of this repository, when the tests
        # run in a worktree of it: the case 'this repository' below then has to get as far as
        # 'inside this repository')
        with tempfile.TemporaryDirectory() as tmp:
            main = self.checkout(tmp, branch='first')
            worktree = os.path.join(tmp, 'worktree')
            self.git(main, 'worktree', 'add', '-q', '-b', 'main', worktree)
            self.assertTrue(os.path.isfile(os.path.join(worktree, '.git')))
            run = self.publish(worktree)
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

    def test_no_leftovers_of_the_tests(self):
        # the tests in the public checkout write ignored files (`__pycache__`, `.kurtc`); they
        # used to stay there and made the next publication refuse it ("ignored files")
        leftovers = 'mkdir -p src/__pycache__ && touch src/__pycache__/x.pyc proofs/x.kurtc'
        for case, test_cmd, ok in [('passing', leftovers, True), ('failing', leftovers + ' && false', False)]:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp:
                public = self.checkout(tmp)
                private = os.path.join(tmp, 'private')   # committed, whatever the working tree here
                self.git(tmp, 'clone', '-q', str(PROJECT_ROOT), private)
                # the public checkout as after the last publication (its diff --check sees changes only)
                subprocess.run(f'git -C {private} archive HEAD | tar -x -C {public}', shell=True, check=True)
                self.git(public, 'add', '-A')
                self.git(public, '-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q', '-m', 'last')
                env = dict(os.environ, PUBLISH_TEST_CMD=test_cmd, GIT_AUTHOR_NAME='t',
                           GIT_AUTHOR_EMAIL='t@t', GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@t')
                run = subprocess.run(['bash', str(SCRIPT), public, 'Kurt test'], cwd=private,
                                     capture_output=True, text=True, env=env)
                self.assertEqual(run.returncode == 0, ok, run.stdout + run.stderr)
                status = subprocess.run(['git', 'status', '--porcelain', '--ignored'], cwd=public,
                                        capture_output=True, text=True, check=True).stdout
                self.assertNotIn('!!', status)
                if ok:
                    self.assertEqual(status, '')
                    self.assertIn('committed in', run.stdout)

if __name__ == '__main__':
    unittest.main()
