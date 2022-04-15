import re
from ..math_mode.identifier import Identifier


SEPARATORS = [",", "and"]
VALIDITY_CHECKS = [
    # even number of $ signs (avoid splitting inside a math mode)
    lambda s: s.count("$") % 2 == 0,
    # even number of $$ (avoid splitting inside a math mode)
    lambda s: s.count("$$") % 2 == 0,
    # no single identifier (avoid separating $a$ and $b$ are integers)
    lambda s: re.fullmatch(Identifier.pattern, s.strip("$ ")) == None,
]


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


def is_valid(string: str):
    """Checks if the string is valid (according to VALIDITY_CHECKS).

    Args:
        string (str): the input string
    """
    for validity_check in VALIDITY_CHECKS:
        if not validity_check(string):
            return False
    return True
