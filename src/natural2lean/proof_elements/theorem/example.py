import re
from natural2lean.utils.printing import subscript
from .theorem import Theorem
from ..propositions.implication import Implication
from ...utils.exceptions import MatchingError

space = r"\s*"


class Example(Theorem):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"(.*)",  # Theorem statement
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # content
        self.statement = Implication(match.group(1))

    def translate(self, **kwargs) -> str:
        hypotheses = self.statement.hypotheses
        theses = self.statement.theses

        lean_identifiers = hypotheses.translate_identifiers()
        lean_hypotheses = " ".join(
            [
                f"(h{subscript(i)} : {h.translate()})"
                for i, h in enumerate(hypotheses.get_non_identifiers())
            ]
        )
        lean_theses = theses.translate()

        arguments = f"{lean_identifiers} {lean_hypotheses}"

        return f"example {arguments} : {lean_theses} := by"
