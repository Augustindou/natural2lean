from __future__ import annotations
from elements.matching_interface import MatchingBaseClass
import re


class Math(MatchingBaseClass):
    """Math block
    @attribute __pattern: str, matches strings of the form ' $ [...] $ '"""

    __pattern: str = r" *\$ *(.+?) *\$ *"

    def __init__(self, string: str) -> None:
        self.string = string
        # TODO : replace expressions such as \cdot, \mod, ...
        # string = string.replace("\mod", "%")
        # TODO : further recursive matching

    @classmethod
    def match(cls, string: str) -> MathExpression:
        m = re.fullmatch(cls.__pattern, string)
        if m == None:
            return None
        return MathExpression(m.group(1))


class MathEquality(MatchingBaseClass):
    """A:MathExpression = B:MathExpression"""

    # TODO : generalize for equality and inequalities


class MathExpression(MatchingBaseClass):
    """Math expression, A:identifier|number <operator> B <operator> C ..."""

    # TODO : work out how to add missing (implied) operators ("3a + 2b" = "3 * a + 2 * b")


class MathIdentifier(MatchingBaseClass):
    """Just an identifier without operator"""


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
