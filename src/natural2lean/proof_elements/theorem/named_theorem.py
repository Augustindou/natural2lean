import re

from natural2lean.utils.printing import subscript


from .theorem import Theorem
from ..propositions.implication import Implication
from ...utils.exceptions import MatchingError

space = r"\s*"


class NamedTheorem(Theorem):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"[Tt]heorem",  # Theorem keyword
            r"(.*)",  # Theorem name
            r":",  # separation between name and statement
            r"(.*)",  # Theorem statement
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # name
        self.latex_name = match.group(1)
        self.lean_name = self.latex_name.lower().replace(" ", "_")
        if self.lean_name[0].isdigit():
            self.lean_name = "_" + self.lean_name

        # content
        self.statement = Implication(match.group(2))

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

        return f"theorem {self.lean_name} {arguments} : {lean_theses} := by"
