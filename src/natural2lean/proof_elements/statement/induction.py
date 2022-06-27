import re
from ...algebra import get_algebra
from ...algebra.identifiers import MultipleIdentifiers
from ...utils.exceptions import MatchingError
from .statement import Statement


space = r"\s*"


class Induction(Statement):
    pattern: str = space.join(
        [
            r"",  # ignore leading space
            r"(.*)",  # anything
            r"(induction)",  # induction keyword
            r"(.*?)",  # anything
            r"(\$.+\$)",  # the variable
            r"(.*)",  # anything
            r"",  # ignore trailing space
        ]
    )

    def __init__(self, string: str, **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match '{string}' in {self.__class__.__name__}."
            )

        # for feedback
        self.match = match

        self.string = string
        expr = get_algebra(match.group(4))

        if isinstance(expr, MultipleIdentifiers) and len(expr.identifiers) == 1:
            self.variable = expr.identifiers[0]
        else:
            raise MatchingError(
                f"Matched {expr.__class__.__name__} in '{self.string}' instead of single identifier."
            )

    def translate(self, **kwargs) -> str:
        return f"match {self.variable.translate()} with"

    def change_status(self) -> bool:
        return True

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        feedback = [
            ("ignored", self.match.group(1)),
            ("keyword", self.match.group(2)),  # "induction"
            ("ignored", self.match.group(3)),
            ("parameter", self.match.group(4)),  # the variable
            ("ignored", self.match.group(5)),
        ]

        return feedback
