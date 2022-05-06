from InquirerPy import inquirer
from ..text.theorem import Example, Theorem
from ..structure.matching import Matching
from ..propositions.multiple_propositions import MultiplePropositions
from ..text.case import Case
from ..text.have import Have
from .lean_feedback import BACKTRACK, FAIL, RESTART, NO_GOALS

BACKTRACK_INDICATORS = ["BACK", "BACKTRACK"]


THEOREM_POSSIBILITIES: list[Matching] = [
    Theorem,
    Example,
]

STATEMENT_POSSIBILITIES: list[Matching] = [
    Case,
    Have,
    MultiplePropositions,
]

# -------------------------------- 
# GET USER INPUT 
# --------------------------------

def theorem_prompt() -> Matching:
    """Asks the user for a theorem and returns the matching object.
    
    Returns:
        Matching: The matching object.
    """
    valid_input = lambda s: match_multiple(s, THEOREM_POSSIBILITIES) is not None
    
    user_input = inquirer.text(
        message="Enter a theorem statement.\n ",
        validate=valid_input,
        invalid_message="Invalid theorem. Try 'theorem [th_name]: if [hyp] then [ccl]' or simply 'if [hyp] then [ccl]'",
    ).execute()
    
    match = match_multiple(user_input, THEOREM_POSSIBILITIES)
    
    return match

def statement_prompt() -> Matching:
    """Asks the user for a statement and returns the matching object.

    Returns:
        Matching: The matching object.
    """
    valid_input = lambda s: match_multiple(s, STATEMENT_POSSIBILITIES) is not None or backtracking_asked(s)
    
    user_input = inquirer.text(
            message="Input a statement\n ",
            validate=valid_input,
            invalid_message="Invalid statement.",
        ).execute()
    print()
    
    if backtracking_asked(user_input):
        return BACKTRACK
    match = match_multiple(user_input, STATEMENT_POSSIBILITIES)
    return match


def match_multiple(input: str, possibilities: list[Matching]) -> Matching:
    for possibility in possibilities:
        try:
            match = possibility.match(input)
        except ValueError:
            match = None
        if match is not None:
            return match
    return None

def backtracking_asked(s: str):
    return s.upper() in BACKTRACK_INDICATORS
    