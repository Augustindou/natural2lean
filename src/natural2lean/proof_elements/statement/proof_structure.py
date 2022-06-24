import re
from typing import Callable

from attr import s
from ...utils.exceptions import MatchingError, TranslationError
from .statement import Statement
from .have import Have


space = r"\s*"


def _contraposition_proof(last_hyp, **kwargs) -> str:
    # if last_hyp is None:
    #     raise ValueError("hyp_name should have been provided, please report this bug.")
    return "\n".join(
        [
            f"revert {last_hyp}",
            f"rw [not_imp_not.symm]",
            f"repeat rw [not_not]",
            f"intro {last_hyp}",
        ]
    )


def _contradiction_proof(hyp_name, **kwargs) -> str:
    # if hyp_name is None:
    #     raise ValueError("hyp_name should have been provided, please report this bug.")
    return "\n".join(
        [
            f"apply not_not.mp",
            f"intro {hyp_name}",
        ]
    )


# if pattern is matched, the string returned by the callable will be added, the last hypothesis will be given as argument
PROOF_STRUCTURES: dict[str, tuple[str, Callable]] = {
    # by contraposition / we will prove the contrapositive / ...
    r"contrapos\w*": _contraposition_proof,
    # we will prove this by contradiction / absurd
    r"(?:contradiction|absurd)": _contradiction_proof,
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
        for key, translation in PROOF_STRUCTURES.items():
            if re.search(key, string):
                self.proof_structure = key
                self.translation = translation
                break

        # possible sub-statement (e.g. when proving the contrapositive, we have ...)
        self.sub_statement = None
        for poss in SUB_STATEMENT_POSSIBILITIES:
            try:
                self.sub_statement: Statement = poss(self.right_side, **kwargs)
            except MatchingError:
                pass

    def translate(self, **kwargs) -> str:
        if not kwargs:
            return self.translation(last_hyp="", hyp_name="hyp")

        if self.sub_statement is None:
            return self.translation(**kwargs)

        return (
            self.translation(**kwargs)
            + "\n\n"
            + self.sub_statement.translate(**kwargs)
        )
