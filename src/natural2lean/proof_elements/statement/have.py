import re
from .statement import Statement
from .such_that import SuchThat
from ...algebra.equation import Equation
from ...propositions.multiple_propositions import MultiplePropositions
from ...propositions.implication import Implication
from ...utils.translatable import Translatable
from ...utils.exceptions import MatchingError, TranslationError

"""
Simple statement such as "we have a contradiction". If the key is matched, the value will be returned by translate. You should consider that the value should already be in tactic mode.
"""
SIMPLE_STATEMENTS: dict[str, str] = {
    r"contradiction": "contradiction",
}

"""
The system will look for matches for the keys in the whole sentence. If a match is found, the value will be passed as proof to sub-statement.
"""
PROOFS: dict[str, str] = {
    r"contradiction": "by contradiction",
    r"definition": "by simp at *; assumption",
    # mod 3 is a bit specific, should extend this to allow for any modulo
    r"possibilities.*modulo": "mod_3_poss _",
    r"modulo.*possibilities": "mod_3_poss _",
}

DEFAULT_PROOF = "by simp at *; assumption"

POSSIBILITIES: list[Translatable] = [Implication, SuchThat, MultiplePropositions]

CALC_PROOF = 1

space = r"\s*"


class Have(Statement):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"(.*)",  # left side
            r"[Hh]ave",  # have keyword
            r"(.*)",  # right side
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}."
            )

        self.string = string
        self.left_side = match.group(1).strip(" ,.;")
        self.right_side = match.group(2).strip(" ,.;")

        self.statement = self.get_statement()
        self.proof = self.get_proof()

    def get_statement(self) -> Translatable:
        for poss in POSSIBILITIES:
            try:
                return poss(self.right_side)
            except MatchingError:
                continue

        for statement in SIMPLE_STATEMENTS:
            if re.search(statement, self.right_side) is not None:
                return SIMPLE_STATEMENTS[statement]

        raise TranslationError(
            f"Could not find a suitable substatement for have in '{self.right_side}'."
        )

    def get_proof(self) -> str:
        # should be proved by calc
        if (
            isinstance(self.statement, MultiplePropositions)
            and len(props := self.statement.propositions) == 1
            and isinstance(props[0], Equation)
        ):
            self.statement = props[0]
            return CALC_PROOF

        for pattern, proof in PROOFS.items():
            if re.search(pattern, self.string.lower()):
                return proof

        # if no proof is given
        return DEFAULT_PROOF

    def translate(self, hyp_name=None, **kwargs) -> str:
        if isinstance(self.statement, str):
            return self.statement
        
        if hyp_name is None:
            return self.statement.translate()

        if self.proof == CALC_PROOF and isinstance(self.statement, Equation):
            return f"have {self.statement.translate(hyp_name=hyp_name, by_calc=True)}"

        return f"have {self.statement.translate(hyp_name=hyp_name, proof=self.proof)}"

    def can_create_new_goals(self) -> bool:
        return self.statement.can_create_new_goals()
