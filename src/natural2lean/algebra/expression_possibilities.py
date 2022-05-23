import re
from .expression import Expression
from .algebra import Algebra
from ..utils.exceptions import MatchingError
from ..utils.unfolding import unfold

space = r"\s*"


class ExpressionPossibilities(Algebra):
    multiple_expressions_pattern = f"(.*?)" + r"(?:(,)(.*))?"
    pattern: str = space.join(
        [
            "",  # ignore leading space
            f"({Expression.pattern})",
            r"∈",
            r"\[",
            f"({multiple_expressions_pattern})",
            r"\]",
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str) -> None:
        # check for match
        match = re.fullmatch(self.pattern, string)
        if not match:
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.string = string.strip()

        # get expression
        self.expression: Expression = Expression(match.group(1))

        # get possibilities
        elements, separators = unfold(self.multiple_expressions_pattern, match.group(2))
        self.possibilities: list[Expression] = [Expression(e) for e in elements]

    def translate(self, hyp_name=None, proof=None, **kwargs) -> str:
        assert (proof is None) == (
            hyp_name is None
        ), "Should always use proof with hyp_name."

        disjunction = " ∨ ".join(
            [
                f"{self.expression.translate()} = {p.translate()}"
                for p in self.possibilities
            ]
        )

        if hyp_name is None:
            return disjunction

        hyp_def = f"{hyp_name} : "
        proof = f" := {proof}"

        hyp = hyp_def + disjunction + proof
        split_goals = f"rcases {hyp_name} with " + " | ".join(
            [hyp_name] * len(self.possibilities)
        )

        return hyp + "\n" + split_goals

    def can_create_new_goals(self) -> bool:
        return True
