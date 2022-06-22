import re
from .have import Have
from .proof_structure import ProofStructure
from .simple_statements import SimpleStatement
from .such_that import SuchThat
from ...propositions.multiple_propositions import MultiplePropositions
from ...algebra.equation import Equation
from ...algebra import get_algebra
from ...algebra.identifiers import MultipleIdentifiers
from ...utils.exceptions import MatchingError
from .statement import Statement


space = r"\s*"


class Induction(Statement):
    pattern: str = space.join(
        [
            r"",  # ignore leading space
            r".+",  # anything
            r"induction",  # induction keyword
            r".+?",  # anything
            r"(\$.+\$)",  # the variable
            r".+",  # anything
            r"",  # ignore trailing space
        ]
    )

    def __init__(self, string: str, **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match '{string}' in {self.__class__.__name__}."
            )

        self.string = string
        expr = get_algebra(match.group(1))

        if isinstance(expr, MultipleIdentifiers) and len(expr.identifiers) == 1:
            self.variable = expr.identifiers[0]
            return

        raise MatchingError(
            f"Matched {expr.__class__.__name__} in '{self.string}' instead of single identifier."
        )

    def translate(self, **kwargs) -> str:
        return f"match {self.variable.translate()} with"

    def change_status(self) -> bool:
        return True


SUB_STATEMENT_POSSIBILITIES = [
    Induction,
    Have,
    ProofStructure,
    SimpleStatement,
]


class InductionCase(Statement):
    """Case will find an equation in the sentence and compare the right side with the variable on which induction is being performed. If they match, it will create the case and check for a possible sub-statement. Otherwise it will raise a MatchingError."""

    def __init__(self, string, proof_status: list[Statement], **kwargs) -> None:
        self.string = string

        # find the first algebraic expression in the string
        alg = get_algebra(string, match_type="search")

        if isinstance(alg, Equation) and len(alg.expressions) == 2:
            self.variable = alg.expressions[0]
            self.expression = alg.expressions[1]
        else:
            raise MatchingError(
                f"The first equation does not correspond to a specific case (such as $n=1$)."
            )

        for statement in proof_status:
            if (
                isinstance(statement, Induction)
                and statement.variable.translate() == self.variable.translate()
            ):
                self.induction = statement
                break
        else:
            # did not find an induction in the proof_status on a corresponding variable
            raise MatchingError(
                f"Could not find an induction with '{self.variable.string}' in the previous statements."
            )

        self.sub_statement = self.get_sub_statement(**kwargs)

    def get_sub_statement(self, **kwargs) -> Statement:
        for poss in SUB_STATEMENT_POSSIBILITIES:
            try:
                return poss(self.string, **kwargs)
            except MatchingError:
                pass

    def translate(self, **kwargs) -> str:
        sub_tr = self.sub_statement.translate(**kwargs) if self.sub_statement else ""
        return f"| {self.expression.translate()} =>\n{sub_tr}"
