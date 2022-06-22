import re

from natural2lean.proof_elements.theorem.theorem import Theorem
from .statement import Statement
from .such_that import SuchThat
from .simple_statements import SimpleStatement
from ...algebra.equation import Equation
from ...propositions.multiple_propositions import MultiplePropositions
from ...propositions.implication import Implication
from ...utils.translatable import Translatable
from ...utils.exceptions import MatchingError, TranslationError
from ...utils.text import indent


"""
The system will look for matches for the keys in the whole sentence. If a match is found, the value will be passed as proof to sub-statement.
"""
SIMPLE_PROOFS: dict[str, str] = {
    r"contradiction": "by contradiction",
    r"definition": "by simp at *; assumption",
    # mod 3 is a bit specific, should extend this to allow for any modulo, but will be easier with mathlib 4
    r"possibilities.*modulo": "mod_3_poss _",
    r"modulo.*possibilities": "mod_3_poss _",
}


def using_theorems(theorems: list[str]) -> str:
    proof = f"repeat (first | ring | simp_all [{', '.join(theorems)}])"
    return "by \n" + indent(proof)


def induction_hypothesis(
    theorems: list[tuple[str, str, str]], n_args: int = 1, **kwargs
) -> str:
    return theorems[-1][1] + " _" * n_args


PARAMETRIC_PROOFS: dict[str, str] = {
    r"induction\s*hypothesis": induction_hypothesis,
}

DEFAULT_PROOF = "by repeat (first | ring | simp_all)"


POSSIBILITIES: list[Translatable] = [
    Implication,
    SuchThat,
    MultiplePropositions,
    SimpleStatement,
]

CALC_PROOF = 1

space = r"\s*"


class Have(Statement):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"(.*)",  # left side
            r"(?:have|derive|give)",  # have keyword
            r"(.*)",  # right side
            "",  # ignore trailing space
        ]
    )

    def __init__(
        self,
        string: str,
        proven_theorems: list[tuple[str, str]],
        **kwargs,
    ) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}."
            )

        self.string = string
        self.left_side = match.group(1).strip(" ,.;")
        self.right_side = match.group(2).strip(" ,.;")

        self.statement = self.get_statement()
        self.proof = self.get_proof(proven_theorems)

    def get_statement(self) -> Translatable:
        for poss in POSSIBILITIES:
            try:
                return poss(self.right_side)
            except MatchingError:
                continue

        raise TranslationError(
            f"Could not find a suitable substatement for have in '{self.right_side}'.\n"
        )

    def get_proof(self, proven_theorems: list[tuple[str, str, str]]) -> str:

        # checking for previously proved theorems
        used_theorems = []
        for latex_th, lean_th in proven_theorems:
            if latex_th.lower() in self.string.lower():
                used_theorems.append(lean_th)

        if used_theorems:
            return using_theorems(used_theorems)

        for pat, param_proof in PARAMETRIC_PROOFS.items():
            if re.search(pat, self.string):
                return param_proof(theorems=proven_theorems)

        # should be proved by calc
        if (
            isinstance(self.statement, MultiplePropositions)
            and len(props := self.statement.propositions) == 1
            and isinstance(props[0], Equation)
        ):
            self.statement = props[0]
            return CALC_PROOF

        for pattern, proof in SIMPLE_PROOFS.items():
            if re.search(pattern, self.string.lower()):
                return proof

        # if no proof is given
        return DEFAULT_PROOF

    def translate(self, hyp_name=None, **kwargs) -> str:
        if hyp_name is None:
            return self.statement.translate()

        if isinstance(self.statement, SimpleStatement):
            return self.statement.translate()

        if self.proof == CALC_PROOF and isinstance(self.statement, Equation):
            have = f"have {self.statement.translate(hyp_name=hyp_name, by_calc=True)}"
            rw = f"try rw [{hyp_name}]"
            return have + "\n" + rw

        return f"have {self.statement.translate(hyp_name=hyp_name, proof=self.proof)}"

    def can_create_new_goals(self) -> bool:
        return self.statement.can_create_new_goals()
