import unittest
from unittest import mock

import kurt.kurt as kurt
import kurt.kurt as kurt_module   # `file_fingerprint` closes over module globals defined
                                   # here, not over `kurt`'s one-time `from .kurt import *`

class TestFileFingerprint(unittest.TestCase):
    def test_normal_case_is_a_12_char_hex_string(self):
        fp = kurt.file_fingerprint()
        self.assertRegex(fp, r'^[0-9a-f]{12}$')

    def test_deterministic(self):
        self.assertEqual(kurt.file_fingerprint(), kurt.file_fingerprint())

    def test_falls_back_to_unknown_if_hashlib_unavailable(self):
        # some exotic/stripped-down Python builds lack hashlib's C backing -- must degrade
        # gracefully (a diagnostic nicety failing shouldn't ever crash startup), not raise
        with mock.patch.object(kurt_module, 'hashlib', None):
            self.assertEqual(kurt.file_fingerprint(), 'unknown')

    def test_falls_back_to_unknown_if_file_unreadable(self):
        with mock.patch('builtins.open', side_effect=OSError('no such file')):
            self.assertEqual(kurt.file_fingerprint(), 'unknown')

if __name__ == '__main__':
    unittest.main()
