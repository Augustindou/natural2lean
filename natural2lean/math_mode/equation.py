import re

from .expression import Expression
from ..structure import Matching
from ..utils import unfold, indent

# TODO : make variations to only allow increasing / decreasing (in)equalities ? (not useful for proof of concept)


class Equation(Matching):
    """Equation class.
    An equation is a sequence of Expressions (`self.expressions`) separated by comparison operators (`self.operators`). `natural2lean.structure.matching` contains useful information to understand the interactions between classes.

    Some examples of Equations (that will be matched) are :
        - a + b < a + b + 1
        - (2 + 3) * 4 > 3
        - a < b ≤ c = d
        - a > b < c ≥ d (this one will be matched but will not work in lean4)
        - ...

    Some more information :
        - The string passed as argument to the constructor must be interpretable by lean4. If it is formatted for LaTex, it has to be processed by `Latex2LeanMath`. See `natural2lean.math_mode.translate_math` for more information.
    """

    pattern: str = (
        # opening group
        r"("
        # first term (? allows to match in a non-greedy way, hence only matching the 1st term)
        r"(.*?)"
        # operators
        r"([=≤≥<>])"
        # second term (can contain equality)
        r"(.*)"
        # closing group
        r")"
    )

    def set_contents(self) -> None:
        elements, separators = unfold(self.pattern, self.string)

        self.expressions: list[Expression] = [Expression(e) for e in elements]
        self.operators: list[str] = separators

    def translate(self, indentation) -> str:
        # keyword for the beginning
        tactic = f"calc\n" 
        # block
        block = f""
        # 1st line
        block += f"{self.expressions[0].translate()} "
        block += f"{self.operators[0]} "
        block += f"{self.expressions[1].translate()}\n"
        # next lines
        for expression, operator in zip(self.expressions[2:], self.operators[1:]):
            block += f"_ {operator} {expression.translate()}\n"
        
        # format complete (standalone) block
        calc_block = tactic + indent(block)
        
        # indent complete block
        return indent(calc_block, indentation)
