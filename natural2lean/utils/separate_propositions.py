import re
from typing import Iterable

from ..math_mode.math import Math
from ..math_mode.multiple_identifiers import MultipleIdentifiers
from ..math_mode.identifier import Identifier

# TODO : Extend to support multiple argument functions

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
    "integer": r"\mathbb{Z}",
}
FUNCTIONS = {
    # matched_function : lean_function
    "even": "even",
    # todo : extend this to support arguments
    "divisible by $3$": "divisible 3",
}
NEGATIONS = {
    "not",
}

# ----------------- SEPARATE PROPOSITIONS -----------------


def separate_propositions(string: str) -> Iterable[str]:
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
            for proposition in split_proposition(string[last_stop:start]):
                yield proposition
            last_stop = stop


def split_proposition(string: str) -> Iterable[str]:
    """Splits a proposition ($a$ and $b$ are even natural numbers) into multiple propositions ($a \\in \\mathbb{N}$, $b \\in \\mathbb{N}$).

    Args:
        string (str): input proposition
    """
    string = apply_replacements(string)

    # match math mode
    math_match = re.search(Math.pattern, string)
    if math_match == None:
        raise Exception("No math content in the proposition")
    math: Math = Math.match(math_match.group(0))

    # set
    if math.is_multiple_identifiers():
        identifiers_set = get_set(string)
        if identifiers_set != None:
            yield f"$ {math.latex_string} \\in {identifiers_set} $"

    # multiple identifiers in set directly in the proposition
    if math.is_identifiers_in_set():
        yield f"$ {math.latex_string} $"

    # functions on identifiers
    if math.is_multiple_identifiers() or math.is_identifiers_in_set():
        function = get_function(string)
        if function != None:
            for identifier in math.content.identifiers:
                yield f"{function} $ {identifier.string} $"

    # functions on math expressions
    if math.is_expression():
        function = get_function(string)
        if function != None:
            yield f"{function} $ {math.latex_string} $"
        else:
            raise ValueError(
                f"Could not find the function related to the expression '{math.latex_string}' in '{string}'."
            )

    # equation (should not have a function associated to it)
    if math.is_equation():
        yield f"$ {math.latex_string} $"


# -------------------- SMALL FUNCTIONS --------------------


def apply_replacements(string: str) -> str:
    """Groups identifiers ($a$ and $b$) into a single math mode ($a, b$).

    Args:
        string (str): the input string
    """
    for pattern, replacement in REPLACEMENTS.items():
        while (match := re.search(pattern, string)) != None:
            string = string[: match.start()] + replacement + string[match.end() :]
    return string


def is_valid(string: str):
    """Checks if the string is valid (according to VALIDITY_CHECKS).

    Args:
        string (str): the input string
    """
    for validity_check in VALIDITY_CHECKS:
        if not validity_check(string):
            return False
    return True


def is_negated(string: str, word: str) -> bool:
    """Checks if the word is negated.

    Args:
        string (str): the input string
        word (str): the word to check
    """
    string = string.lower()
    word = word.lower()
    idx = string.find(word)
    if idx == -1:
        return False
    if string[:idx].split()[-1] in NEGATIONS:
        return True
    return False


# ------------------ EXTRACT INFORMATION ------------------


def get_set(string: str):
    """Extracts the set associated to the proposition.

    Args:
        string (str): the input string
    """
    string = string.lower()
    matched_set = None
    for word, set_definition in SETS.items():
        if word in string:
            if matched_set != None:
                raise Exception("Multiple sets in the same proposition")
            matched_set = set_definition
    return matched_set


def get_function(string: str):
    """Extracts the function associated to the proposition.

    Args:
        string (str): the input string
    """
    matched_function = None
    for latex_function, lean_function in FUNCTIONS.items():
        if latex_function in string:
            if matched_function != None:
                raise Exception(
                    f"Multiple functions in the same proposition : in '{string}', '{latex_function}' and '{matched_function}'were found"
                )
            matched_function = lean_function
    if is_negated(string, latex_function):
        matched_function = f"¬ {matched_function}"
    return matched_function
