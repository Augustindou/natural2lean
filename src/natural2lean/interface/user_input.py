from InquirerPy import inquirer
from ..structure.matching import Matching
from ..text.theorem import Example, Theorem
from ..text.have import Have
from ..propositions.multiple_propositions import MultiplePropositions
from .lean_feedback import BACKTRACK, EXIT

KEYWORDS = {
    BACKTRACK: ("BACKTRACK", "BACK"),
    EXIT: ("EXIT", "QUIT", "STOP"),
}

THEOREM_POSSIBILITIES: list[Matching] = [
    Theorem,
    Example,
]

STATEMENT_POSSIBILITIES: list[Matching] = [
    Have,
    MultiplePropositions,
]

# --------------------------------
# GET USER INPUT
# --------------------------------


def theorem_prompt(default="") -> Matching:
    """Asks the user for a theorem and returns the matching object.

    Returns:
        Matching: The matching object.
    """
    valid_input = (
        lambda s: match_multiple(s, THEOREM_POSSIBILITIES) is not None
        or keyword_status_code(s) is not None
    )

    user_input = inquirer.text(
        message="Enter a theorem statement.\n ",
        validate=valid_input,
        invalid_message="Invalid theorem. Try 'theorem [th_name]: if [hyp] then [ccl]' or simply 'if [hyp] then [ccl]'",
        default=default,
    ).execute()

    print()

    if (status_code := keyword_status_code(user_input)) is not None:
        return status_code

    match = match_multiple(user_input, THEOREM_POSSIBILITIES)
    return match, user_input


def statement_prompt(default="") -> Matching:
    """Asks the user for a statement and returns the matching object.

    Returns:
        Matching: The matching object.
    """
    valid_input = (
        lambda s: match_multiple(s, STATEMENT_POSSIBILITIES) is not None
        or keyword_status_code(s) is not None
    )

    user_input = inquirer.text(
        message="Input a statement.\n ",
        validate=valid_input,
        invalid_message="Invalid statement.",
        default=default,
    ).execute()

    print()

    if (status_code := keyword_status_code(user_input)) is not None:
        return status_code

    match = match_multiple(user_input, STATEMENT_POSSIBILITIES)
    return match, user_input


def match_multiple(input: str, possibilities: list[Matching]) -> Matching:
    for possibility in possibilities:
        try:
            match = possibility.match(input)
        except ValueError:
            match = None
        if match is not None:
            return match
    return None


def keyword_status_code(s: str) -> int:
    for status_code, keywords in KEYWORDS.items():
        if s.upper() in keywords:
            return status_code
    return None
