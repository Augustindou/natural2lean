import re
from .theorem import Theorem, STATEMENT_POSSIBILITIES
from ...utils.exceptions import MatchingError

space = r"\s*"


class NamedTheorem(Theorem):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"([Tt]heorem|[Ll]emma)",  # Theorem keyword
            r"(.*)",  # Theorem name
            r"(:)",  # separation between name and statement
            r"(.*)",  # Theorem statement
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str, **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # keep it for processing in interpretation_feedback()
        self.match = match

        # name
        self.latex_name = match.group(2)
        self.lean_name = self.latex_name.lower().replace(" ", "_")
        if self.lean_name[0].isdigit():
            self.lean_name = "_" + self.lean_name

        # content
        for poss in STATEMENT_POSSIBILITIES:
            try:
                self.statement = poss(match.group(4))
                self.set_hypotheses_and_theses()
                return
            except MatchingError:
                pass

        raise MatchingError(
            f"Could not match any statement to prove for {string}, tried {', '.join([p.__name__ for p in STATEMENT_POSSIBILITIES])}."
        )

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        feedback = [
            ("keyword", self.match.group(1)),
            ("parameter", self.match.group(2)),
            ("keyword", self.match.group(3)),
        ]

        return feedback + self.statement.interpretation_feedback()

    # translate method is inherited
