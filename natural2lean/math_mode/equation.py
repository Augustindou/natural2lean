import re
from .expression import Expression
from ..structure import Matching
from ..utils import unfold


class Equation(Matching):
    pattern = (
        # opening group
        r"(" 
        # first term (? allows to match in a non-greedy way)
        r"(.*?)"
        # equality sign
        r"([=≤≥<>])"
        # second term (can contain equality)
        r"(.*)"
        # closing group
        r")"
    )

    def __get_contents(self) -> None:
        elements, separators = unfold(self.pattern, self.string)
        
        self.expressions: list[Expression] = [Expression(e) for e in elements]
        self.equality_signs: list[str] = separators

    def translate(self) -> str:
        raise NotImplementedError
