import re
from typing import Callable
from .have import Have
from .statement import Statement
from .induction import Induction
from .simple_statements import SimpleStatement
from ...utils.exceptions import MatchingError


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
    r"[Cc]ontrapos\w*": _contraposition_proof,
    # we will prove this by contradiction / absurd
    r"(?:[Cc]ontradiction|[Aa]bsurd)": _contradiction_proof,
}

SUB_STATEMENT_POSSIBILITIES: list = [Have, Induction, SimpleStatement]

space = r"\s*"


class ProofStructure(Statement):
    pattern: str = space.join(
        [
            r"",  # ignore leading space
            r"(.*)",  # anything
            f"({'|'.join(PROOF_STRUCTURES.keys())})",  # proof_structure
            r"(.*)",  # possible sub statement
            r"",  # ignore trailing space
        ]
    )

    def __init__(self, string: str, **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}."
            )

        # for feedback
        self.match = match

        self.string = string
        self.right_side = match.group(3)

        # retrieve which proof_structure it is
        for key, translation in PROOF_STRUCTURES.items():
            if re.fullmatch(key, match.group(2)):
                self.proof_structure = key
                self.translation = translation
                break

        # possible sub-statement (e.g. when proving the contrapositive, we have ...)
        self.sub_statement = self.get_sub_statement(**kwargs)

    def get_sub_statement(self, **kwargs) -> Statement:
        for poss in SUB_STATEMENT_POSSIBILITIES:
            try:
                return poss(self.right_side, **kwargs)
            except MatchingError:
                pass

    def translate(self, **kwargs) -> str:
        if not kwargs:
            return self.translation(last_hyp="", hyp_name="hyp")

        if self.sub_statement is None:
            return self.translation(**kwargs)

        return (
            self.translation(**kwargs) + "\n\n" + self.sub_statement.translate(**kwargs)
        )

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        if self.sub_statement is None:
            sub_statement_feedback = [("ignored", self.right_side)]
        else:
            sub_statement_feedback = self.sub_statement.interpretation_feedback()

        feedback = [
            ("ignored", self.match.group(1)),
            ("keyword", self.match.group(2)),
        ]

        return feedback + sub_statement_feedback
