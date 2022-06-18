import re
from typing import Callable
from ...utils.exceptions import MatchingError
from .statement import Statement
from .have import Have


space = r"\s*"

_contraposition_proof = lambda last_hyp: "\n".join(
    [
        f"revert {last_hyp}",
        f"rw [not_imp_not.symm]",
        f"repeat rw [not_not]",
        f"intro {last_hyp}",
    ]
)


# if pattern is matched, the string returned by the callable will be added, the last hypothesis will be given as argument
PROOF_STRUCTURES: dict[str, Callable] = {
    # by contraposition / we will prove the contrapositive / ...
    r"contrapos\w*": _contraposition_proof,
    # r"contradiction": lambda last_hyp: "todo",
}

SUB_STATEMENT_POSSIBILITIES: list = [Have]


class ProofStructure(Statement):
    pattern: str = f"(?:{'|'.join(PROOF_STRUCTURES.keys())})"

    def __init__(self, string: str, **kwargs) -> None:
        if not (match := re.search(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}."
            )

        self.string = string
        self.right_side = string[match.end() :]

        # retrieve which proof_structure it is
        for key, value in PROOF_STRUCTURES.items():
            if re.search(key, string):
                self.proof_structure = key
                self.translation = value
                break

        # possible sub-statement (e.g. when proving the contrapositive, we have ...)
        self.sub_statement = None
        for poss in SUB_STATEMENT_POSSIBILITIES:
            try:
                self.sub_statement: Statement = poss(self.right_side, **kwargs)
            except MatchingError:
                pass

    def translate(self, last_hyp=None, **kwargs) -> str:
        if last_hyp is None:
            return " "

        if self.sub_statement is None:
            return self.translation(last_hyp)

        return (
            self.translation(last_hyp) + "\n\n" + self.sub_statement.translate(**kwargs)
        )
