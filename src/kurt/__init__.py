# Kurt as a library: check a proof given as text or as a file, e.g.
#
#     import kurt
#     result = kurt.check_text('load prop\nbool A, B\nuse A implies B\nuse A\nB\n')
#     result.ok, result.complete, result.output, result.error
#
# A session has its own options (`RunConfig`: strict, paths, kurtc) and state; checks in one
# process don't influence each other. The internals are in `kurt.kurt` (not a stable API).
from .kurt import (version, RunConfig, CheckResult, Session, new_session, check_text, check_file,
                   KurtException, main)

__all__ = ['version', 'RunConfig', 'CheckResult', 'Session', 'new_session', 'check_text', 'check_file',
           'KurtException', 'main']
