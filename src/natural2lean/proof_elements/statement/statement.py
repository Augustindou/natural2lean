from .have import Have
from .such_that import SuchThat
from ...utils.translatable import Translatable
from ...utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [Have, SuchThat]


class Statement(Translatable):
    def __init__(self, string: str) -> None:
        self.string = string

        for poss in POSSIBILITIES:
            try:
                self.statement = poss(self.string)
                return
            except MatchingError:
                pass

        raise TranslationError(
            f"Could not match any statement for {self.string}, tried "
            + ", ".join([p.__name__ for p in POSSIBILITIES])
        )


def get_statement(string: str) -> Statement:
    return Statement(string).statement
