from .example import Example
from .named_theorem import NamedTheorem
from ...utils.translatable import Translatable
from ...utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [NamedTheorem, Example]


class Theorem(Translatable):
    def __init__(self, string: str):
        self.string = string

        for poss in POSSIBILITIES:
            try:
                self.theorem = poss(self.string)
                return
            except MatchingError:
                pass

        raise TranslationError(
            f"Could not match any theorem for {self.string}, tried "
            + ", ".join([p.__name__ for p in POSSIBILITIES])
        )


def get_theorem(string: str) -> Theorem:
    return Theorem(string).theorem
