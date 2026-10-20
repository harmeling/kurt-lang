# Kurt as a library: check a proof given as text or as a file, e.g.
#
#     import kurt
#     result = kurt.check_text('load propositional\nbool A, B\nuse A implies B\nuse A\nB\n')
#     result.ok, result.complete, result.output, result.error
#
# A session has its own options (`RunConfig`: strict, paths, kurtc) and state; checks in one
# process don't influence each other. The internals are in `kurt.kurt` (not a stable API) -- imported
# when first used, so that `python -m kurt.kurt FILE` runs it once (no "found in sys.modules" warning).

__all__ = ['version', 'RunConfig', 'CheckResult', 'Session', 'Shell', 'new_session', 'check_text', 'check_file',
           'KurtException', 'main']


def __getattr__(name: str):
    if name in __all__:
        from . import kurt as _kurt
        return getattr(_kurt, name)
    raise AttributeError(f'module {__name__!r} has no attribute {name!r}')
