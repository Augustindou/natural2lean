from dataclasses import dataclass


@dataclass(frozen=True)
class LatexFunction:
    pattern: str
    separators: list[str]


@dataclass(frozen=True)
class MathSet:
    latex: str
    intermediate: str
    lean: str
    full_words: tuple[str]


"""
The characters used to group function arguments.
"""
START_OF_FUNCTION = "{"
END_OF_FUNCTION = "}"

"""
For each set, 
- the first argument should be its representation in LaTeX, 
- the second can be anything, an intermediate representation that is used. It should not be something that will be interpreted in another way in lean.
- the third argumetn is the representation in lean.
- the last argument contains a tuple of words that a user could type to refer to the set.
"""
SETS: dict[str, MathSet] = {
    "ℕ": MathSet(r"\mathbb{N}", "ℕ", "Nat", ("natural",)),
    # "ℤ": MathSet(r"\mathbb{Z}", "ℤ", "Int", ("integer",)), # not compatible with the current work, because header considers that we are working with Naturals
    # "ℚ": MathSet(r"\mathbb{Q}", "ℚ", "???", , ("rational,")), # Rationals not implemented in lean yet ?
    # "ℝ": MathSet(r"\mathbb{R}", "ℝ", "???", ("real,")), # Reals not implemented in lean yet ?
    # "ℂ": MathSet(r"\mathbb{C}", "ℂ", "???", ("complex,")), # Complexes not implemented in lean yet ?
}

"""
The keys will be replaced by the corresponding values when translating a math expression from LaTeX to Lean. 
"""
LATEX_SYMBOLS: dict[str, str] = {
    # remove new lines
    "\n": "",
    # operations
    r"\mod": r"%",
    r"\cdot": r"*",
    # parenthesis
    r"\bigg": r"",
    r"\left": r"",
    r"\right": r"",
    # equalities / inequalities
    r"\eq": r"=",
    r"\neq": r"≠",
    r"\leq": r"≤",
    r"\geq": r"≥",
    r"\lt": r"<",
    r"\gt": r">",
    # for sets, all the sets in SETS will be added at the end and should not be added here
    r"\in": r"∈",
    r"\times": r"×",
    # to allow for sets such as a, b \in \{a, b\}
    r"\{": r"{",
    r"\}": r"}",
}

"""
Here, the separators will be added before the first argument, between arguments and after the last argument. The pattern should be a regex pattern, you should therefore watch out for special characters. Some translations are specific to the translation system (e.g. [] will be recognized by ExpressionPossibilities).

The arguments of the LatexFunction dataclass are:
    - `pattern` : str, regex pattern to match the start of the LaTeX function.
    - `separators` : list[str], the separators before, between and after the arguments of the LaTeX function. There must therefore be one more separator than the number of arguments of the LaTeX function (e.g. the \\frac function has 2 arguments (numerator and denominator) and therefore 3 separators).
"""
LATEX_FUNCTIONS: list[LatexFunction] = [
    # watch out for special regex characters (^, $, ., ?, *, +, |, (, ), [, ], {, }, \)
    LatexFunction(r"\\frac *{", ["((", ") / (", "))"]),
    LatexFunction(r"\\sqrt *{", ["((", ") ^ (1/2))"]),
    LatexFunction(r"\^ *{", ["^(", ")"]),
    LatexFunction(r"_ *{", ["_", ""]),
    LatexFunction(r"∈ *{", ["∈ [", "]"]),
]

"""
Here, the values (implicit operation) will be placed before the key's last regex group. The keys should be a regex pattern, you should therefore watch out for special characters. There is no reason I can think of to have more than one group in the regex pattern, but the system will not fail if there are.
"""
IMPLICIT_OPERATIONS: dict[str, str] = {
    # 2(x + y) -> 2 * (x + y)
    r"\w *(\()": "*",
    # (x + y)2 -> (x + y) * 2
    r"\) *(\w)": "*",
    # 2x2 -> 2 * x2
    r"(?:^|\W)\d+ *( *[a-zA-Z]\w* *)": "*",
    # (x + y)(z + w) -> (x + y) * (z + w)
    r"\) *(\()": "*",
}


# ----------------------------------------------------------
# Adding sets to symbols
# ----------------------------------------------------------

for s in SETS.values():
    if s.latex in LATEX_SYMBOLS:
        raise ValueError(
            f"The translation {s.latex} => {s.intermediate} could not be added to the symbol dictionary because {s.latex} was already there."
        )

    LATEX_SYMBOLS[s.latex] = s.intermediate
