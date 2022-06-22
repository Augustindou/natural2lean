from .example import Example
from .named_theorem import NamedTheorem
from .theorem import Theorem
from ...utils.exceptions import MatchingError, TranslationError

POSSIBILITIES = [NamedTheorem, Example]


def get_theorem(string: str, **kwargs) -> Theorem:
    for poss in POSSIBILITIES:
        try:
            return poss(string, **kwargs)
        except MatchingError:
            pass

    raise TranslationError(
        f"Could not match any theorem for '{string}', tried "
        + ", ".join([p.__name__ for p in POSSIBILITIES])
        + ".\n"
    )
