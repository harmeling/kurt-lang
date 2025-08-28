# match the theory against a a list of expressions (not the other way around) and grow the substitution
def match_all_theory(expr: Expr, kb: KnowledgeBase) -> tuple[bool, list[Formula]]:
    debug(f'expr: [{expr_str(expr, kb)}]')

    # iterate over all formulas of the theory
    for candidate in kb.all_theory():
        # iterate over all possible substitutions that create a match
        # IMPORTANT: match the candidate to the expression (not vice versa)
        optional_subst = _first_or_none(match_exprs([(candidate.simplified_expr, expr)], {}, kb))
        if optional_subst is not None:
            return True, [candidate]

    # no match so far, however, possibly `expr` is a conjunction that we can split into pieces
    match expr:
        # e.g., (A and B) implies C, then `expr = ['and', A, B]`
        case [Token(label='SYMBOL', value=v), *exprs] if v == AND_SYMBOL and len(exprs) > 1:
            candidates: list[Formula] = []
            for e in exprs:
                success, new_candidates = match_all_theory(e, kb)
                if not success:
                    break      # sorry!  no match for expression 'e'
                candidates.extend(new_candidates)
            else:
                return True, candidates

