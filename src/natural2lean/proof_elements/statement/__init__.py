from .have import Have
from .such_that import SuchThat
from .statement import Statement
from ...propositions.multiple_propositions import MultiplePropositions
from ...utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [Have, SuchThat, MultiplePropositions]


def get_statement(string: str) -> Statement:
    for poss in POSSIBILITIES:
        try:
            return poss(string)
        except MatchingError:
            pass

    raise TranslationError(
        f"Could not match any statement for {string}, tried "
        + ", ".join([p.__name__ for p in POSSIBILITIES])
    )
