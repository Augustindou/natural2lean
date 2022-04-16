import re
from ..math_mode.multiple_identifiers import MultipleIdentifiers
from ..math_mode.identifier import Identifier


# ---------------------- PARAMETERS ----------------------

VALIDITY_CHECKS = [
    # even number of $ signs (avoid splitting inside a math mode)
    lambda s: s.count("$") % 2 == 0,
    # even number of $$ (avoid splitting inside a math mode)
    lambda s: s.count("$$") % 2 == 0,
    # no single identifier (avoid separating $a$ and $b$ are integers)
    lambda s: re.fullmatch(Identifier.pattern, s.strip("$ ")) == None,
    # no multiple identifiers
    lambda s: MultipleIdentifiers.match(apply_replacements(s).strip("$ ")) == None,
]
SEPARATORS = [",", "and"]
REPLACEMENTS = {
    r"\$ *and *\$": ", ",
    r"\$ *, *\$": ", ",
}
SETS = {
    "natural": r"\mathbb{N}",
}
FUNCTIONS = {
    "even": "even",
}

# ----------------- SEPARATE PROPOSITIONS -----------------


def separate_propositions(string: str):
    """Separates multiple propositions (PropA, PropB and PropC).

    Args:
        string (str): the input string
    """
    # to yield the last proposition too ;)
    separator_spans = [(len(string), len(string))]
    # get all the spans for the separators
    for separator in SEPARATORS:
        separator_spans += [m.span() for m in re.finditer(separator, string)]
    separator_spans = sorted(separator_spans)

    # yield different propositions
    last_stop = 0
    for start, stop in separator_spans:
        if is_valid(string[last_stop:start]):
            yield string[last_stop:start]
            last_stop = stop


def split_proposition(string: str):
    """Splits a proposition ($a$ and $b$ are even natural numbers) into multiple propositions ($a \\in \\mathbb{N}$, $b \\in \\mathbb{N}$).

    Args:
        string (str): input proposition
    """
    string = apply_replacements(string)

    # get set(s?) associated to the proposition
    # get the functions associated to the proposition
    # find a way to return the functions (and the sets) associated to the proposition
    #           L=> Have a class "math concept" returning the good representation when calling .translate() ?


def apply_replacements(string: str) -> str:
    """Groups identifiers ($a$ and $b$) into a single math mode ($a, b$).

    Args:
        string (str): the input string
    """
    for pattern, replacement in REPLACEMENTS.items():
        while (match := re.search(pattern, string)) != None:
            string = string[: match.start()] + replacement + string[match.end() :]


# ----------------------- VALIDITY -----------------------


def is_valid(string: str):
    """Checks if the string is valid (according to VALIDITY_CHECKS).

    Args:
        string (str): the input string
    """
    for validity_check in VALIDITY_CHECKS:
        if not validity_check(string):
            return False
    return True
