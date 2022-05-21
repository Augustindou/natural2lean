import re
from .translate_math import translate_latex_math
from ..utils.exceptions import MatchingError
from ..utils.translatable import Translatable


space = r"\s*"


class Algebra(Translatable):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"\${1,2}",
            r"(.+?)",
            r"\${1,2}",
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str, match_type: str = "full"):
        if match_type.lower() in ("fullmatch", "full"):
            matcher = re.fullmatch
        elif match_type.lower() in ("search", "partial"):
            matcher = re.search
        else:
            raise ValueError(f"match_type should be either 'full' or 'search'")
        if not (match := matcher(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.latex_string = f"$ {match.group(1).strip()} $"
        self.lean_string = translate_latex_math(self.latex_string.strip("$"))
