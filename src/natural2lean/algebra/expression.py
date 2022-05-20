import re
from .algebra import Algebra
from ..utils.exceptions import MatchingError


class Expression(Algebra):
    # anything (an expression can be only a single term, a numeric value or a computation (x+y))
    pattern: str = r".*"

    def __init__(self, string: str) -> None:
        # possible errors
        if string.strip() == "":
            raise MatchingError(
                f"Could not match empty string in {self.__class__.__name__}"
            )
        if re.match(r"[≠=<≤>≥]", string):
            raise MatchingError(
                f"Could {self.__class__.__name__} cannot contain equality operators"
            )

        self.string = string.strip()

    def translate(self, **kwargs) -> str:
        return self.string
