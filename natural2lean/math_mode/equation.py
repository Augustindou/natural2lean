import re

from .expression import Expression
from ..structure.matching import Matching
from ..utils.unfolding import unfold
from ..utils.indentation import indent


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
        - The string passed as argument to the constructor must be interpretable by lean4. If it is formatted for LaTex, it has to be processed by `translate_latex_math`. See `natural2lean.utils.translate_math` for more information.
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

    def detect_errors(self):
        # check for more than one inequality
        if re.fullmatch(r".*≠.*≠.*", self.string):
            raise ValueError(
                f"Only one inequality sign is allowed to conclude anything about the left- and rightmost terms, but found at least 2 in {self.string}"
            )

        # check for increasing and decreasing inequalities
        if re.fullmatch(r".*[<≤].*[≥>].*", self.string) or re.fullmatch(
            r".*[≥>].*[<≤].*", self.string
        ):
            raise ValueError(
                f"An equation is allowed to increase (</≤/=) or decrease (>/≥/=) to conclude anything about the left- and rightmost terms, but found at least 1 relation operator in each direction in {self.string}"
            )

        # check for [<>≤≥] and ≠
        if re.fullmatch(r".*[<>≤≥].*[≠].*", self.string) or re.fullmatch(
            r".*[≠].*[<>≤≥].*", self.string
        ):
            raise ValueError(
                f"An equation is allowed to be increasing, decreasing or have an inequality sign to conclude anything about the left- and rightmost terms, but found a mix in {self.string}"
            )

        super().detect_errors()

    def translate(self) -> str:
        return " ∧ ".join(
            f"{self.expressions[i].translate()} {self.operators[i]} {self.expressions[i+1].translate()}"
            for i in range(len(self.operators))
        )

    def translate_to_calc(self, indentation: int = 0) -> str:
        # keyword for the beginning
        tactic = f"calc\n"
        # block
        block = f""
        # 1st line
        block += f"{self.expressions[0].translate()} "
        block += f"{self.operators[0]} "
        block += f"{self.expressions[1].translate()}"
        # proof of 1st line
        block += f" := by"
        block += f"try simp [*];"  # simplify with all hypotheses
        block += f"try ring\n"
        # next lines
        for expression, operator in zip(self.expressions[2:], self.operators[1:]):
            block += f"_ {operator} {expression.translate()} := by ring\n"

        # format complete (standalone) block
        calc_block = tactic + indent(block)

        # indent complete block
        return indent(calc_block, indentation)

    def get_strongest_operator(self) -> str:
        if "≠" in self.operators:
            return "≠"

        if ">" in self.operators:
            return ">"

        if "<" in self.operators:
            return "<"

        if "≤" in self.operators:
            return "≤"

        if "≥" in self.operators:
            return "≥"

        return "="

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return (
                self.expressions == other.expressions
                and self.operators == other.operators
            )
        return False
