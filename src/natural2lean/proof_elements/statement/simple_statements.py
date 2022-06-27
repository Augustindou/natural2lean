import re
from .statement import Statement
from ...utils.exceptions import MatchingError


"""
Simple statement such as "we have a contradiction". If the key is matched, the value will be returned by translate. You should consider that the value should already be in tactic mode.
"""
SIMPLE_STATEMENTS: dict[str, str] = {
    r"contradiction": "contradiction",
    r"trivial": "repeat (first | trivial | ring | simp_all)",
}

space = r"\s*"


class SimpleStatement(Statement):
    pattern: str = space.join(
        [
            r"",  # ignore leading space
            r"(.*)",  # anything
            f"({'|'.join(SIMPLE_STATEMENTS.keys())})",  # statement
            r"(.*)",  # anything
            r"",  # ignore trailing space
        ]
    )

    def __init__(self, string, **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}."
            )

        # for feedback
        self.match = match

        self.string = string

        # retrieve which proof_structure it is
        for key, translation in SIMPLE_STATEMENTS.items():
            if re.fullmatch(key, match.group(2)):
                self.statement = key
                self.translation = translation
                break

    def translate(self, **kwargs) -> str:
        return self.translation

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        feedback = [
            ("ignored", self.match.group(1)),
            ("keyword", self.match.group(2)),
            ("ignored", self.match.group(3)),
        ]

        return feedback
