import re
from ..utils.exceptions import TranslationError
from .translation_constants import (
    START_OF_FUNCTION,
    END_OF_FUNCTION,
    LATEX_SYMBOLS,
    LATEX_FUNCTIONS,
    IMPLICIT_OPERATIONS,
    LatexFunction,
)


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
            raise TranslationError(
                f"LaTeX function without end"
                + f'\n        in "{self.latex_string}"'
                + f'\n        at "{self.latex_string[next_function_start:]}"'
                + "\n"
            )

        # end found before start
        if next_start_start == None or next_end_start < next_start_start:
            self.result_string += self.latex_string[position:next_end_start]
            return next_end_end

        # function found
        if next_start_start < next_end_start and next_function_start < next_start_start:
            # add part before function
            self.result_string += self.latex_string[position:next_function_start]

            for i in range(len(next_function.separators) - 1):
                # go to next argument
                next_start_start, next_start_end = self.get_next_start(position)
                next_end_start, next_end_end = self.get_next_end(position)

                # if some argument is missing START_OF_FUNCTION
                if next_start_start == None:
                    raise TranslationError(
                        f"LaTeX function with wrong number of arguments"
                        + f'\n        in "{self.latex_string}"'
                        + f'\n        at "{self.latex_string[next_function_start:]}"'
                        + "\n"
                    )

                # add intermediate elements (between args of function)
                self.result_string += next_function.separators[i]

                # add ith argument
                position = self.function_replacement(next_start_end)

                # if some argument is missing END_OF_FUNCTION
                if position == -1:
                    raise TranslationError(
                        f"Missing argument for latex function"
                        + f'\n        in "{self.latex_string}"'
                        + f'\n        at "{self.latex_string[next_function_start:]}"'
                        + "\n"
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
