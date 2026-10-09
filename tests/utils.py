# utils.py
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]



def with_quantifiers(kb):
    # `forall`/`exists` as logic.kurt declares them -- the core has no quantifiers (2026-10-09),
    # and these unit tests check the binder handling on a bare knowledge base
    import kurt.kurt as kurt
    for q in ('forall', 'exists'):
        kb.add_arity(q, 2)
        kb.add_bindop(q)
        kb.add_bool(q, [0, 2])
    kb.bind_engine_role('forall', 'universal')
    kb.bind_engine_role('exists', 'existential')
    kurt.symbols_changed()
    return kb


def numbered(output: str, line: int, reason: str) -> bool:
    # whether the output shows source line `line` (its number in front) with `reason` (`by 3(4)`),
    # as Kurt prints it: `   5  B          ; by 3(4)`
    import re
    rows = output.splitlines()
    for i, row in enumerate(rows):
        if re.match(rf'^\s*{line}  ', row):
            # its reason, or on the next line (after a comment of its own)
            if re.search(rf';\s*{re.escape(reason)}', row) or \
                    (i + 1 < len(rows) and re.match(rf'^\s*;\s*{re.escape(reason)}', rows[i + 1])):
                return True
    return False
