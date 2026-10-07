import re
import unittest

from tests.utils import PROJECT_ROOT

# the README says how many lessons there are: it must be right (dev/astra-suggestions.md)


class TestReadmeCounts(unittest.TestCase):
    def test_the_lesson_counts(self):
        readme = (PROJECT_ROOT / 'README.md').read_text(encoding='utf-8')
        for directory, phrase in [('tutorial', r'the tutorial, (\d+) lessons \(00 to (\d+)\)'),
                                  ('keywords', r'(\d+) short lessons \(00 to (\d+)\)')]:
            with self.subTest(directory=directory):
                lessons = sorted(p.name for p in (PROJECT_ROOT / directory).glob('[0-9][0-9]-*.kurt'))
                found = re.search(phrase, readme)
                self.assertIsNotNone(found, phrase)
                self.assertEqual(int(found.group(1)), len(lessons))
                self.assertEqual(found.group(2), lessons[-1][:2])

if __name__ == '__main__':
    unittest.main()
