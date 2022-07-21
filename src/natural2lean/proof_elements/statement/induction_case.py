import re
from .have import Have
from .induction import Induction
from .proof_structure import ProofStructure
from .simple_statements import SimpleStatement
from ...algebra.equation import Equation
from ...algebra import get_algebra
from ...utils.exceptions import MatchingError
from .statement import Statement

space = r"\s*"

SUB_STATEMENT_POSSIBILITIES = [
    Induction,
    Have,
    ProofStructure,
    SimpleStatement,
]


class InductionCase(Statement):
    """Case will find an equation in the sentence and compare the right side with the variable on which induction is being performed. If they match, it will create the case and check for a possible sub-statement. Otherwise it will raise a MatchingError."""

    pattern: str = space.join(
        [
            r"",  # ignore leading space
            r"(.*?)",  # anything ("for", ...)
            r"(\$.+?\$)",  # the variable ("$n = 0$", ...)
            r"(.*)",  # potential sub-statement
            r"",  # ignore trailing space
        ]
    )

    def __init__(self, string, proof_status: list[Statement], **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match '{string}' in {self.__class__.__name__}."
            )

        # for feedback
        self.match = match

        self.string = string
        self.right_side = match.group(3)

        # find the first algebraic expression in the string
        alg = get_algebra(match.group(2))

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
                return poss(self.right_side, **kwargs)
            except MatchingError:
                pass

    def translate(self, **kwargs) -> str:
        if self.sub_statement:
            sub_tr = self.sub_statement.translate(**kwargs)
        else:
            sub_tr = ""

        return f"| {self.expression.translate()} =>\nskip\n{sub_tr}"

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        if self.sub_statement is None:
            sub_statement_feedback = [("ignored", self.right_side)]
        else:
            sub_statement_feedback = self.sub_statement.interpretation_feedback()

        feedback = [
            ("ignored", self.match.group(1)),
            ("parameter", self.match.group(2)),
        ]

        return feedback + sub_statement_feedback
