import re
import unittest

from tests.utils import PROJECT_ROOT

# a release publishes nothing (PyPI, the standalone kurt.py) before the tests pass: each job of
# release.yml but `verify` needs it (dev/astra-suggestions.md, release gating)


class TestReleaseWorkflow(unittest.TestCase):
    def test_every_publishing_job_needs_verify(self):
        text = (PROJECT_ROOT / '.github' / 'workflows' / 'release.yml').read_text(encoding='utf-8')
        jobs = re.split(r'^  (?=[a-z]+:\n)', text.split('\njobs:\n', 1)[1], flags=re.M)
        jobs = {job.split(':', 1)[0]: job for job in jobs if job.strip()}
        self.assertIn('verify', jobs)
        self.assertIn('python -m unittest', jobs['verify'])
        self.assertEqual(set(jobs) - {'verify'}, {'pypi', 'standalone'})
        for name, job in jobs.items():
            if name != 'verify':
                with self.subTest(job=name):
                    self.assertRegex(job, r'\n    needs: verify\n')

if __name__ == '__main__':
    unittest.main()
