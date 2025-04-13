# replacements.py
import re

REPLACEMENTS = {
    # propositional logic
    "\\not":     "¬",
    "\\neg":     "¬",
    "\\and":     "∧",
    "\\or":      "∨",
    "\\iff":     "⇔",
    "\\implies": "⇒",
    "\\bottom":  "⊥",
    "\\top":     "⊤",

    # first order logic
    "\\forall":  "∀",
    "\\exists":  "∃",

    # modal logic
    "\\box":     "□",      # necessity
    "\\b":       "□",
    "\\diamond": "◇",      # possibility
    "\\d":       "◇",

    # set theory
    "\\infty": "∞",        # infinity
    "\\in": "∈",           # element of
    "\\notin": "∉",        # not element of
    "\\subset": "⊂",       # proper subset
    "\\subseteq": "⊆",     # subset or equal
    "\\supset": "⊃",       # proper superset
    "\\supseteq": "⊇",     # superset or equal
    "\\cap": "∩",          # intersection
    "\\cup": "∪",          # union
    "\\emptyset": "∅",     # empty set
    "\\equiv": "≡",        # equivalence
    "\\leq": "≤",          # less than or equal
    "\\geq": "≥",          # greater than or equal

    # small greek letters
    "\\alpha":   "α",
    "\\beta":    "β",
    "\\gamma":   "γ",
    "\\delta":   "δ",
    "\\epsilon": "ε",
    "\\zeta":    "ζ",
    "\\eta":     "η",
    "\\theta":   "θ",
    "\\iota":    "ι",
    "\\kappa":   "κ",
    "\\lambda":  "λ",
    "\\mu":      "μ",
    "\\nu":      "ν",
    "\\xi":      "ξ",
    "\\omicron": "ο",
    "\\pi":      "π",
    "\\rho":     "ρ",
    "\\sigma":   "σ",
    "\\tau":     "τ",
    "\\upsilon": "υ",
    "\\phi":     "φ",
    "\\chi":     "χ",
    "\\psi":     "ψ",
    "\\omega":   "ω",

    # capital greek letters
    "\\Alpha":   "Α",
    "\\Beta":    "Β",
    "\\Gamma":   "Γ",
    "\\Delta":   "Δ",
    "\\Epsilon": "Ε",
    "\\Zeta":    "Ζ",
    "\\Eta":     "Η",
    "\\Theta":   "Θ",
    "\\Iota":    "Ι",
    "\\Kappa":   "Κ",
    "\\Lambda":  "Λ",
    "\\Mu":      "Μ",
    "\\Nu":      "Ν",
    "\\Xi":      "Ξ",
    "\\Omicron": "Ο",
    "\\Pi":      "Π",
    "\\Rho":     "Ρ",
    "\\Sigma":   "Σ",
    "\\Tau":     "Τ",
    "\\Upsilon": "Υ",
    "\\Phi":     "Φ",
    "\\Chi":     "Χ",
    "\\Psi":     "Ψ",
    "\\Omega":   "Ω"
}

# for the scanner
SPECIAL_SYMBOLS = ''.join(sorted(set(''.join(REPLACEMENTS.values()))))

# Precompiled regex to match all \commands
COMMAND_RE = re.compile(r'\\[a-zA-Z]+')

# Optional: precompute the unique symbol characters used in replacements
REPLACEMENT_SYMBOLS = ''.join(set(REPLACEMENTS.values()))
REPLACEMENT_SYMBOLS_RE = re.compile(
    rf'([{re.escape(REPLACEMENT_SYMBOLS)}])(  +| )'
)

def replace_latex_syntax(line: str) -> str:
    def command_replacer(match):
        command = match.group(0)
        return REPLACEMENTS.get(command, command)

    # Step 1: Replace all \commands
    line = COMMAND_RE.sub(command_replacer, line)

    # Step 2: Postprocess spacing
    # Replace double+ spaces after symbol → one space
    # Replace single space after symbol → no space
    line = REPLACEMENT_SYMBOLS_RE.sub(lambda m: m.group(1) + (' ' if m.group(2).startswith('  ') else ''), line)

    return line