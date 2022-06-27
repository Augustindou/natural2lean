import re
from .theorem import Theorem, STATEMENT_POSSIBILITIES
from ...utils.text import subscript
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

    def __init__(self, string: str, i: int) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.latex_name = f"th{i}"
        self.lean_name = f"th{i}"

        # content
        for poss in STATEMENT_POSSIBILITIES:
            try:
                self.statement = poss(match.group(1))
                self.set_hypotheses_and_theses()
                return
            except MatchingError:
                pass

        raise MatchingError(
            f"Could not match any statement to prove for {string}, tried {', '.join([p.__name__ for p in STATEMENT_POSSIBILITIES])}."
        )

    def interpretation_feedback(self) -> list[tuple[str, str]]:

        return self.statement.interpretation_feedback()

    # translate method is inherited
