from .have import Have
from .such_that import SuchThat
from .statement import Statement
from ...propositions.multiple_propositions import MultiplePropositions
from ...utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [Have, SuchThat]
# conclusions, statements that would only be accepted if they are conclusions of a goal
CCL_POSSIBILITIES = [MultiplePropositions]


def get_statement(string: str) -> Statement:
    for poss in POSSIBILITIES + CCL_POSSIBILITIES:
        try:
            return poss(string)
        except MatchingError:
            pass

    raise TranslationError(
        f"Could not match any statement for {string}, tried "
        + ", ".join([p.__name__ for p in POSSIBILITIES])
    )
