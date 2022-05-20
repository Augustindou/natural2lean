import re
from typing import Callable, Iterable
from ..utils.exceptions import TranslationError
from ..utils.translate_math import translate_latex_math
from ..structure.matching import Translatable
from ..math_mode.math import Math
from ..math_mode.multiple_identifiers import MultipleIdentifiers
from ..math_mode.identifier import Identifier
from ..math_mode.expression import Expression
from ..propositions.function import Function


# ---------------------- PARAMETERS ----------------------

get_lean_math = lambda s: translate_latex_math(apply_replacements(s).strip("$ "))
VALIDITY_CHECKS: list[Callable] = [
    # even number of $ signs (avoid splitting inside a math mode)
    lambda s: s.count("$") % 2 == 0,
    # even number of $$ (avoid splitting inside a math mode)
    lambda s: s.count("$$") % 2 == 0,
    # no single identifier (avoid separating $a$ and $b$ are integers)
    lambda s: Identifier.match(get_lean_math(s)) == None,
    # no multiple identifiers alone
    lambda s: MultipleIdentifiers.match(get_lean_math(s)) == None,
    # no expression alone
    lambda s: Expression.match(get_lean_math(s)) == None,
]
SEPARATORS: list[str] = [",", "and"]
NEGATIONS: list[str] = ["not"]
# keys will be replaced by values
REPLACEMENTS: dict[str, str] = {
    # remove all single $
    r"\$\$": "$",
    r"\$ *and *\$": ", ",
    r"\$ *, *\$": ", ",
}
SETS: dict[str, str] = {
    "natural": "\\mathbb{N}",
    "integer": "\\mathbb{Z}",
}
# tuple of function name, function pattern, and callable to rearrange function arguments (keep_order and invert_order are examples, but one can also directly use a lambda function for more specific needs)
# pattern must contain one group for each argument
keep_order = lambda *args: args
invert_order = lambda *args: args[::-1]
FUNCTIONS: list[tuple[str, str, Callable]] = {
    ("even", r"(\$.*?\$).*?even", keep_order),
    (
        "divisible",
        r"(\$.*?\$).*?divisible\s*by.*?(\$.*?\$)",
        invert_order,
    ),
}

# ----------------- SEPARATE PROPOSITIONS -----------------


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


def split_proposition(string: str):
    """Splits a proposition ($a$ and $b$ are even natural numbers) into multiple propositions ($a \\in \\mathbb{N}$, $b \\in \\mathbb{N}$).

    Args:
        string (str): input proposition
    """
    string = apply_replacements(string)

    # match math mode
    math_match = re.search(Math.pattern, string)
    if math_match == None:
        raise TranslationError("No math content in the proposition")
    math: Math = Math.match(math_match.group(0))

    # set
    if math.is_multiple_identifiers():
        identifiers_set = get_set(string)
        if identifiers_set != None:
            yield Math.match(
                "$"
                + ", ".join([ident.string for ident in math.content.identifiers])
                + " \\in "
                + identifiers_set
                + "$"
            ).content

    # multiple identifiers in set directly in the proposition
    if math.is_identifiers_in_set():
        yield math.content

    # functions on identifiers
    if (
        math.is_multiple_identifiers()
        or math.is_identifiers_in_set()
        or math.is_expression()
    ):
        for function in get_functions(string):
            yield function

    # equation (should not have a function associated to it)
    if math.is_equation():
        yield math.content


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


def get_functions(string: str) -> Iterable[Function]:
    """Extracts the functions associated to the proposition.

    Args:
        string (str): the input string
    """
    for name, pattern, order_arguments in FUNCTIONS:
        name = f"¬ {name}" if contains_negation(string) else name
        match = re.search(pattern, string)

        # skip if no match
        if match == None:
            continue

        # match arguments
        args: list[Math] = [Math.match(group) for group in match.groups()]

        # first group can be multiple identifiers
        if args[0].is_multiple_identifiers() or args[0].is_identifiers_in_set():
            for identifier in args[0].content.identifiers:
                yield Function(name, order_arguments(*[identifier, *args[1:]]), string)
            continue

        if args[0].is_expression():
            yield Function(name, order_arguments(*args), string)
            continue
