import re
from typing import Callable
from ..utils.exceptions import MatchingError
from ..algebra.algebra import Algebra
from ..algebra.identifiers import MultipleIdentifiers

# TODO COMMENTS
REPLACEMENTS: dict[str, str] = {
    r"\$\$": "$",
    r"\$\s*and\s*\$": ", ",
    r"\$\s*,\s*\$": ", ",
}
SEPARATORS: list[str] = [",", "and"]
NEGATIONS: list[str] = ["not", "n't"]

# tuple of function name, function pattern, and callable to rearrange function arguments (keep_order and invert_order are examples, but one can also directly use a lambda function for more specific needs)
# pattern must contain one group for each argument
keep_order = lambda *args: args
invert_order = lambda *args: args[::-1]
# even groups are arguments, all groups will be highlighted by interpretation_feedback, use empty groups if needed ;)
FUNCTIONS: list[tuple[str, str, Callable]] = [
    ("even", r"(\$.+?\$).*?(even)", keep_order),
    ("odd", r"(\$.+?\$).*?(odd)", keep_order),
    (
        "divisible",
        r"(\$.+?\$).*?(divisible\s*by).*?(\$.+?\$)",
        invert_order,
    ),
]
# ------------- VALIDITY CHECKS -------------


def matches_algebra(string: str, cls: type) -> bool:
    try:
        cls(get_lean_math(string))
        return True
    except MatchingError:
        return False


VALIDITY_CHECKS: list[Callable] = [
    # even number of $ signs (avoid splitting inside a math mode)
    lambda s: s.count("$") % 2 == 0,
    # no identifiers alone
    lambda s: not matches_algebra(s, MultipleIdentifiers),
]


# ---------------- SMALL FUNCTIONS -----------------
def get_lean_math(string: str) -> str:
    al = Algebra(apply_replacements(string))
    return al.lean_string


def apply_replacements(string: str) -> str:
    """Groups identifiers ($a$ and $b$) into a single math mode ($a, b$).

    Args:
        string (str): the input string
    """
    for pattern, replacement in REPLACEMENTS.items():
        while (match := re.search(pattern, string)) != None:
            string = string[: match.start()] + replacement + string[match.end() :]
    return string
