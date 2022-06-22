from __future__ import annotations
from .algebra import Algebra
from .equation import Equation
from .expression import Expression
from .expression_possibilities import ExpressionPossibilities
from .identifiers import IdentifiersInSet, MultipleIdentifiers
from ..utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [
    Equation,
    ExpressionPossibilities,
    IdentifiersInSet,
    MultipleIdentifiers,
    Expression,
]


def get_algebra(latex_string: str, match_type: str = "full") -> Algebra:
    algebra = Algebra(latex_string, match_type=match_type)

    for poss in POSSIBILITIES:
        try:
            return poss(algebra.lean_string)
        except MatchingError:
            pass

    raise TranslationError(
        f"Could not match any algebra for '{latex_string}', tried "
        + ", ".join([p.__name__ for p in POSSIBILITIES])
        + ".\n"
    )
