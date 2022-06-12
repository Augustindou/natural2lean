from natural2lean.proof_elements.statement.such_that import SuchThat
from .have import Have
from .proof_structure import ProofStructure
from .statement import Statement
from ...propositions.multiple_propositions import MultiplePropositions
from ...utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [Have, ProofStructure]
# conclusions, statements that would only be accepted if they are conclusions of a goal
CCL_POSSIBILITIES = [MultiplePropositions, SuchThat]


def get_statement(string: str, **kwargs) -> Statement:
    for poss in POSSIBILITIES + CCL_POSSIBILITIES:
        try:
            return poss(string, **kwargs)
        except MatchingError:
            pass

    raise TranslationError(
        f"Could not match any statement for '{string}', tried "
        + ", ".join([p.__name__ for p in POSSIBILITIES])
    )
