import re
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# the version is set in src/kurt/kurt.py only (pyproject.toml reads it from there); CITATION.cff
# and CHANGELOG.md name it too, so a new version must change them as well


class TestVersionsAgree(unittest.TestCase):
    def test_citation_names_the_version(self):
        citation = (PROJECT_ROOT / 'CITATION.cff').read_text(encoding='utf-8')
        found = re.search(r'^version:\s*(\S+)', citation, re.MULTILINE)
        self.assertIsNotNone(found, 'no version in CITATION.cff')
        self.assertEqual(found.group(1), kurt.version)

    def test_changelog_has_the_version(self):
        changelog = (PROJECT_ROOT / 'CHANGELOG.md').read_text(encoding='utf-8')
        self.assertRegex(changelog, rf'(?m)^## {re.escape(kurt.version)} ')


if __name__ == '__main__':
    unittest.main()
