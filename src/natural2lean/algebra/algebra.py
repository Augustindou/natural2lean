import re
from __future__ import annotations
from .equation import Equation
from .expression import Expression
from .expression_possibilities import ExpressionPossibilities
from .identifiers import IdentifiersInSet, MultipleIdentifiers
from .translate_math import translate_latex_math
from ..utils.exceptions import MatchingError, TranslationError
from ..utils.translatable import Translatable

POSSIBILITIES = [
    Equation,
    ExpressionPossibilities,
    IdentifiersInSet,
    MultipleIdentifiers,
    Expression,
]


space = r"\s*"


class Algebra(Translatable):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"\${1,2}",
            r".+?",
            r"\${1,2}",
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str):
        if not re.fullmatch(self.pattern, string):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.latex_string = string.strip()
        self.lean_string = translate_latex_math(self.latex_string.strip("$"))

        for poss in POSSIBILITIES:
            try:
                self.statement = poss(self.lean_string)
                return
            except MatchingError:
                pass

        raise TranslationError(
            f"Could not match any statement for {self.latex_string}, tried "
            + ", ".join([p.__name__ for p in POSSIBILITIES])
        )


def get_algebra(latex_string: str) -> Algebra:
    return Algebra(latex_string).statement
