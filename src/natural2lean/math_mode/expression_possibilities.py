import re
from ..utils.unfolding import unfold
from .set import Set
from .expression import Expression
from ..structure.matching import Matching


class ExpressionPossibilities(Matching):
    """ExpressionPossibilities class.

    - a ∈ __POSS__[1, 2, 3]
    - a + b ∈ __POSS__[1, 2, 3]
    - ...
    """

    #   *(([+\-*/^%(). ]*(?:\w)+(?:\w|\s|[+\-*/^%(). ])*) *(∈) *(__POSS__\[.*\])) *
    pattern: str = (
        # opening group
        r" *("
        # expression
        r""
        + Expression.pattern
        + r""
        # in specific set
        r"*(∈) *(__POSS__\[.*\])) *"
    )

    def set_contents(self) -> None:
        match = re.fullmatch(self.pattern, self.string)

        # possibilities
        self.relation_to_set = match.group(3).strip()
        self.possibilities: Possibilities = Possibilities.match(match.group(4).strip())

        # match the expression
        self.expression = Expression(match.group(2))
        
    def detect_errors(self):
        if self.possibilities == None:
            raise ValueError(f"Problem with identifying the different possibilities (between '{{' and '}}') in {self.string}")
        return super().detect_errors()

    def translate(self, hyp=None, proof="", **kwargs) -> str:
        disjunction = self.possibilities.translate(expr=self.expression.translate())

        if hyp is not None:
            tr = f"{hyp} : " + disjunction + proof
            split_goals = f"rcases {hyp} with " + " | ".join(
                [hyp] * len(self.possibilities.poss)
            )
            return tr + "\n" + split_goals

        return disjunction

    def can_create_new_goals(self) -> bool:
        return True


class Possibilities(Matching):
    """Possibilities class.

    - a ∈ {1, 2, 3}
    TODO
    """

    pattern = r"\s*(__POSS__\[(.*)\])\s*"

    unfold_match = (
        # opening 1st group
        r" *("
        # group for expression
        r"("
        + Expression.pattern[1:-1]
        + r")"
        # separator (comma)
        r" *(?:(,) *"
        # group for following expressions
        r"("
        + Expression.pattern[1:-1]
        + r"(?: *, *"
        + Expression.pattern[1:-1]
        + r")*) *)*) *"
    )

    def set_contents(self) -> None:
        # set of possibilities ({1, 2, 3} which will have been translated into __POSS__[1, 2, 3])
        if (match := re.fullmatch(self.pattern, self.string)) is not None:
            elements, separators = unfold(self.unfold_match, match.group(2))
            self.poss = [Expression.match(element) for element in elements]

    def detect_errors(self):
        if any([e == None for e in self.poss]):
            raise ValueError(
                f"The system does not understand the set in '{self.string}'"
            )

        return super().detect_errors()

    def translate(self, expr=None, **kwargs) -> str:
        if expr is not None:
            return " ∨ ".join([f"{expr} = {poss.translate()}" for poss in self.poss])

        raise ValueError(
            f"Problem translating.\n  identifier: {expr} \n  string: {self.string}"
        )
