import re
from typing import Iterable

from .function import Function
from .proposition_constants import (
    SEPARATORS,
    NEGATIONS,
    FUNCTIONS,
    VALIDITY_CHECKS,
    apply_replacements,
)
from ..algebra import (
    get_algebra,
    Algebra,
    Equation,
    Expression,
    IdentifiersInSet,
    MultipleIdentifiers,
)
from ..utils.exceptions import MatchingError, TranslationError
from ..utils.translatable import Translatable
from ..algebra.translation_constants import SETS, MathSet
from ..algebra.expression_possibilities import ExpressionPossibilities


# ------------------ MAIN FUNCTIONS ------------------


def get_propositions(string: str) -> list[Translatable]:
    return [prop for prop in separate_propositions(string)]


def separate_propositions(string: str) -> Iterable[Translatable]:
    """Separates multiple propositions (PropA, PropB and PropC).

    Args:
        string (str): the input string
    """
    # also yield the last proposition ;)
    separator_spans = [(len(string), len(string))]

    # get all the spans for the separators
    for separator in SEPARATORS:
        separator_spans += [m.span() for m in re.finditer(separator, string)]
    separator_spans = sorted(separator_spans)

    # yield different propositions
    last_stop = 0
    for start, stop in separator_spans:
        if is_valid(string[last_stop:start]):
            for proposition in split_proposition(string[last_stop:start]):
                yield proposition
            last_stop = stop


def split_proposition(string: str) -> Iterable[Translatable]:
    """Splits a proposition ($a$ and $b$ are even natural numbers) into multiple propositions ($a \\in \\mathbb{N}$, $b \\in \\mathbb{N}$).

    Args:
        string (str): input proposition
    """
    string = apply_replacements(string)

    # match math mode
    try:
        math = get_algebra(string, match_type="partial")
    except MatchingError:
        math = None

    # set
    if isinstance(math, MultipleIdentifiers):
        set_ = get_set(string)
        if set_:
            if isinstance(math, IdentifiersInSet):
                raise TranslationError(
                    f"Multiple sets in the same proposition; found '{set_}' and '{math.set.latex}' in '{string}'\n"
                )

            algebra = get_algebra("$" + math.string + " \\in " + set_.latex + "$")
            assert isinstance(algebra, IdentifiersInSet)
            yield algebra

    # multiple identifiers in set directly in the proposition
    if isinstance(math, IdentifiersInSet):
        yield math

    # functions on identifiers or expressions
    if (
        isinstance(math, MultipleIdentifiers)
        or isinstance(math, Expression)
        or isinstance(math, ExpressionPossibilities)
    ):
        for function in get_functions(string):
            yield function

    # equation (should not have a function associated to it)
    if isinstance(math, Equation) or isinstance(math, ExpressionPossibilities):
        yield math


# ------------------ EXTRACT INFORMATION ------------------


def get_set(string: str) -> MathSet:
    """Extracts the set associated to the proposition.

    Args:
        string (str): the input string
    """
    string = string.lower()
    matched_set = None
    for set_ in SETS.values():
        for word in set_.full_words:
            if word in string:
                if matched_set != None:
                    raise TranslationError(
                        f"Multiple sets in the same proposition; found '{prev_word}' and '{word}' in '{string}'\n"
                    )
                matched_set = set_
                prev_word = word

    return matched_set


def get_functions(string: str) -> Iterable[Function]:
    """Extracts the functions associated to the proposition.

    Args:
        string (str): the input string
    """
    for name, pattern, order_arguments in FUNCTIONS:
        # skip if no match
        if (match := re.search(pattern, string)) is None:
            continue

        # negate function
        name = f"¬ {name}" if contains_negation(string) else name
        # match arguments
        args: list[Algebra] = [get_algebra(arg) for arg in match.groups()]

        # first group can be multiple identifiers
        if isinstance(args[0], MultipleIdentifiers):
            for identifier in args[0].identifiers:
                yield Function(name, order_arguments(*[identifier, *args[1:]]))
            continue

        if isinstance(args[0], Expression):
            yield Function(name, order_arguments(*args))
            continue


# ---------------- SMALL UTILITY FUNCTIONS ----------------


def is_valid(string: str):
    """Checks if the string is valid (according to VALIDITY_CHECKS).

    Args:
        string (str): the input string
    """
    for validity_check in VALIDITY_CHECKS:
        if not validity_check(string):
            return False
    return True


def contains_negation(string: str) -> bool:
    """Checks a negation is present in the string

    Args:
        string (str): the input string
    """
    string = string.lower()
    for neg in NEGATIONS:
        if neg in string:
            return True
    return False
