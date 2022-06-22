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


class SimpleStatement(Statement):
    def __init__(self, string, **kwargs) -> None:
        self.string = string

        # check each key
        for pattern in SIMPLE_STATEMENTS:
            if re.search(pattern, self.string):
                self.keyword = pattern
                return

        raise MatchingError(f"Could not match {string} in {self.__class__.__name__}.")

    def translate(self, **kwargs) -> str:
        return SIMPLE_STATEMENTS[self.keyword]
