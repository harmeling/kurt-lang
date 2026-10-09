import os
import tempfile
import unittest

import kurt.kurt as kurt

# a session checks a loaded file once (`_checked_exports`) -- and again when one of its `load`s
# would now find another file: a new one earlier in the search path, or a link that points
# elsewhere (dev/astra-suggestions.md, finding 4)


def write(path, text):
    with open(path, 'w', encoding='utf-8') as f:
        f.write(text)


class TestLoadCache(unittest.TestCase):
    def setUp(self):
        self.cwd = os.getcwd()
        self.tmp = tempfile.TemporaryDirectory()
        self.teacher = os.path.join(self.tmp.name, 'teacher')
        self.student = os.path.join(self.tmp.name, 'student')
        os.mkdir(self.teacher)
        os.mkdir(self.student)
        write(os.path.join(self.teacher, 'dep.kurt'), 'bool P\nuse P "given"\n')
        write(os.path.join(self.student, 'helper.kurt'), 'load dep\nP "result"\n')
        write(os.path.join(self.student, 'main.kurt'), 'load helper\nP\n')
        os.chdir(self.student)          # (the working directory comes first in the search path)

    def tearDown(self):
        os.chdir(self.cwd)
        self.tmp.cleanup()

    def check(self, session):
        return session.check_file(os.path.join(self.student, 'main.kurt'))

    def test_a_new_file_earlier_in_the_search_path(self):
        session = kurt.new_session(kurt.RunConfig(paths=(self.teacher,)))
        self.assertTrue(self.check(session).ok)
        write(os.path.join(self.student, 'dep.kurt'), 'bool P\nP "given"\n')     # unproven
        fresh = self.check(kurt.new_session(kurt.RunConfig(paths=(self.teacher,))))
        self.assertFalse(fresh.ok)
        again = self.check(session)
        self.assertEqual((again.ok, again.error), (fresh.ok, fresh.error))

    def test_a_link_that_points_elsewhere(self):
        if not hasattr(os, 'symlink'):
            self.skipTest('no symbolic links')
        os.remove(os.path.join(self.teacher, 'dep.kurt'))
        write(os.path.join(self.teacher, 'given.kurt'), 'bool P\nuse P "given"\n')
        write(os.path.join(self.teacher, 'other.kurt'), 'bool P\n')
        link = os.path.join(self.teacher, 'dep.kurt')
        os.symlink('given.kurt', link)
        session = kurt.new_session(kurt.RunConfig(paths=(self.teacher,)))
        self.assertTrue(self.check(session).ok)
        os.remove(link)
        os.symlink('other.kurt', link)
        self.assertFalse(self.check(kurt.new_session(kurt.RunConfig(paths=(self.teacher,)))).ok)
        self.assertFalse(self.check(session).ok)

    def test_a_changed_file(self):
        session = kurt.new_session(kurt.RunConfig(paths=(self.teacher,)))
        self.assertTrue(self.check(session).ok)
        write(os.path.join(self.teacher, 'dep.kurt'), 'bool P\n')
        self.assertFalse(self.check(session).ok)

    def test_an_unchanged_file_is_checked_once(self):
        session = kurt.new_session(kurt.RunConfig(paths=(self.teacher,)))
        self.assertTrue(self.check(session).ok)
        self.assertTrue(len(session._state._checked_exports) >= 2)       # helper and dep
        with session._active():
            entries = list(kurt.run_state._checked_exports.values())
            self.assertTrue(all(kurt.same_load_resolutions(e[2]) for e in entries))
        self.assertTrue(self.check(session).ok)

if __name__ == '__main__':
    unittest.main()
