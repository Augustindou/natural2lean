from dataclasses import dataclass
import re

# TODO : how to handle x_{1 2} and x_{1, 2} ? (not useful for proof of concept)

"""Translate Math
This whole file is dedicated to the translation of math from latex to lean. The translation can be done by calling `translate_latex_math(latex_string)`. It can be extended to handle other operations, in different ways.

- `LATEX_SYMBOLS` : dict[str, str]
    - keys : latex symbols
    - values : equivalent lean symbols
    - The keys will simply be replaced by the values (using `str.replace(k, v)`).
- `IMPLICIT_OPERATIONS` : dict[str, str]
    - keys : regex containing at least one group
    - values : implicit operation to insert
    - The implicit operation will be inserted before the last group in the regex.
- `LATEX_FUNCTIONS` : list[LatexFunction]. each LatexFunction contains:
    - `pattern` : str, regex pattern to match the start of the LaTeX function.
    - `n_args` : int, the number of arguments of the LaTeX function.
    - `separators` : list[str], the separators before, between and after the arguments of the LaTeX function.
"""


@dataclass
class LatexFunction:
    pattern: str
    n_args: int
    separators: list[str]


START_OF_FUNCTION = "{"
END_OF_FUNCTION = "}"
LATEX_SYMBOLS = {
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
    # for sets
    r"\in": r"∈",
    r"\mathbb{N}": r"ℕ",
    r"\mathbb{Z}": r"ℤ",
    r"\mathbb{Q}": r"ℚ",
    r"\mathbb{R}": r"ℝ",
    r"\mathbb{C}": r"ℂ",
    # to allow for sets such as a, b \in \{a, b\}
    r"\{": r"{",
    r"\}": r"}",
    # remove new lines
    "\n": "",
}
LATEX_FUNCTIONS = [
    # watch out for special regex characters (^, $, ., ?, *, +, |, (, ), [, ], {, }, \)
    LatexFunction(r"\\frac *{", 2, ["((", ") / (", "))"]),
    LatexFunction(r"\\sqrt *{", 1, ["((", ") ^ (1/2))"]),
    LatexFunction(r"\^ *{", 1, ["^(", ")"]),
    LatexFunction(r"_ *{", 1, ["_", ""]),
    LatexFunction(r"∈ *{", 1, ["∈ __SET__[", "]"]),
]
IMPLICIT_OPERATIONS = {
    # 2(x + y) -> 2 * (x + y)
    r"\w *(\()": "*",
    # (x + y)2 -> (x + y) * 2
    r"\) *(\w)": "*",
    # 2x2 -> 2 * x2
    r"(?:^|\W)\d+ *( *[a-zA-Z]\w* *)": "*",
    # (x + y)(z + w) -> (x + y) * (z + w)
    r"\) *(\()": "*",
}


class Latex2LeanMath:
    """Translation from LaTeX math (`a\\frac{a + 1}{b^2}`) to lean4 math (`a * ((a+1) / (b^2))`) can be done by calling `str(Latex2LeanMath(latex_string))` or simply `translate_latex_math(latex_string)`"""

    def __init__(self, latex_string: str) -> None:
        self.latex_string = latex_string
        self.result_string = ""
        self.symbol_replacement()
        self.function_replacement()
        self.implicit_operations()

    def symbol_replacement(self):
        for k, v in LATEX_SYMBOLS.items():
            self.latex_string = self.latex_string.replace(k, v)

    def function_replacement(self, position: int = 0) -> int:
        next_function_start, next_function_end, next_function = self.get_next_function(
            position
        )
        next_start_start, next_start_end = self.get_next_start(position)
        next_end_start, next_end_end = self.get_next_end(position)

        # no function or arg
        if (
            next_function == None
            and next_start_start == None
            and next_end_start == None
        ):
            self.result_string += self.latex_string[position:]
            return -1

        # function without end
        if next_end_start == None:
            raise Exception(
                f"LaTeX function without end"
                + f'\n        in "{self.latex_string}"'
                + f'\n        at "{self.latex_string[next_function_start:]}"'
            )

        # end found before start
        if next_start_start == None or next_end_start < next_start_start:
            self.result_string += self.latex_string[position:next_end_start]
            return next_end_end

        # function found
        if next_start_start < next_end_start and next_function_start < next_start_start:
            # add part before function
            self.result_string += self.latex_string[position:next_function_start]

            for i in range(next_function.n_args):
                # go to next argument
                next_start_start, next_start_end = self.get_next_start(position)
                next_end_start, next_end_end = self.get_next_end(position)

                # if some argument is missing START_OF_FUNCTION
                if next_start_start == None:
                    raise Exception(
                        f"LaTeX function with wrong number of arguments"
                        + f'\n        in "{self.latex_string}"'
                        + f'\n        at "{self.latex_string[next_function_start:]}"'
                    )

                # add intermediate elements (between args of function)
                self.result_string += next_function.separators[i]

                # add ith argument
                position = self.function_replacement(next_start_end)

                # if some argument is missing END_OF_FUNCTION
                if position == -1:
                    raise Exception(
                        f"Missing argument for latex function"
                        + f'\n        in "{self.latex_string}"'
                        + f'\n        at "{self.latex_string[next_function_start:]}"'
                    )

            # add last element of function
            self.result_string += next_function.separators[i + 1]

            position = self.function_replacement(position)
            return position

        raise Exception(f"Should not happen - Latex2LeanMath.function_replacement")

    def implicit_operations(self):
        still_matching = len(IMPLICIT_OPERATIONS)

        while still_matching > 0:
            still_matching = len(IMPLICIT_OPERATIONS)

            # match all patterns
            for pattern, operation in IMPLICIT_OPERATIONS.items():
                match_pattern = re.search(pattern, self.result_string)

                # if no match
                if match_pattern == None:
                    still_matching -= 1
                    continue

                # get the position for the added '*'
                end = match_pattern.end()
                right_term = match_pattern.groups()[-1]
                position = end - len(right_term)

                self.result_string = (
                    self.result_string[:position]
                    + operation
                    + self.result_string[position:]
                )

    def get_next_function(self, position: int) -> tuple[int, int, LatexFunction]:
        starts = []

        for tex_fun in LATEX_FUNCTIONS:
            match_function = re.search(tex_fun.pattern, self.latex_string[position:])

            # no match for this latex function
            if match_function == None:
                continue

            # add to list
            next_function_start = match_function.start() + position
            next_function_end = match_function.end() + position
            starts.append((next_function_start, next_function_end, tex_fun))

        if len(starts) == 0:
            return None, None, None

        return min(starts)

    def get_next_end(self, position: int) -> int:
        # check for next end
        match_end = re.search(END_OF_FUNCTION, self.latex_string[position:])

        # no end found
        if match_end == None:
            return None, None

        next_end_start = match_end.start() + position
        next_end_end = match_end.end() + position

        return next_end_start, next_end_end

    def get_next_start(self, position: int) -> int:
        # check for next start
        match_start = re.search(START_OF_FUNCTION, self.latex_string[position:])

        # no start found
        if match_start == None:
            return None, None

        next_start_start = match_start.start() + position
        next_start_end = match_start.end() + position

        return next_start_start, next_start_end

    def __str__(self) -> str:
        return self.result_string


def translate_latex_math(latex_string: str) -> str:
    return str(Latex2LeanMath(latex_string))