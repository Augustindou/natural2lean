import re

from .expression import Expression
from .algebra import Algebra
from ..utils.unfolding import unfold
from ..utils.text import indent
from ..utils.exceptions import MatchingError


class Equation(Algebra):
    pattern: str = r"(.*?)([≠=<≤>≥])(.*)"

    def __init__(self, string: str):
        # check for match
        if not re.fullmatch(self.pattern, string):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.string = string

        elements, separators = unfold(self.pattern, self.string)
        self.expressions: list[Expression] = [Expression(e) for e in elements]
        self.operators: list[str] = separators

    def translate(
        self, hyp_name: str = None, proof: str = None, by_calc: bool = False, **kwargs
    ) -> str:
        # sanity check
        assert not (proof is not None and by_calc), "Can't use both proof and by_calc"

        # proof
        if by_calc:
            proof = f" := by \n{indent(self.calc_block())}"
        elif proof is None:
            proof = ""
        else:
            proof = f" := {proof}"

        # hypothesis definition
        hyp_def = f"{hyp_name} : " if hyp_name else ""
        hyp = (
            hyp_def
            + self.expressions[0].translate()
            + f" {self.strongest_operator()} "
            + self.expressions[-1].translate()
        )

        return hyp + proof

    def calc_block(self) -> str:
        LINE_PROOF = f"repeat (first | ring | simp_all)"
        # keyword for the beginning
        tactic = f"calc\n"
        # 1st line
        block = f"{self.expressions[0].translate()} {self.operators[0]} {self.expressions[1].translate()}"
        # proof of 1st line
        block += f" := by {LINE_PROOF}"
        # next lines
        for expression, operator in zip(self.expressions[2:], self.operators[1:]):
            block += "\n"
            block += f"_ {operator} {expression.translate()} := by {LINE_PROOF}"

        # format complete (standalone) block
        return tactic + indent(block)

    def strongest_operator(self) -> str:
        # order of operations, from most loose to most strict
        ORDER = ["≠", ">", "<", "≥", "≤", "="]
        for op in ORDER:
            if op in self.operators:
                return op

        raise Exception(f"No operator found in {self.string}, should not get here.")
