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
    r"(.*)(contradiction)(.*)": "by contradiction",
    r"(.*)(definition)(.*)": "by simp at *; assumption",
    # mod 3 is a bit specific, should extend this to allow for any modulo, but will be easier with mathlib 4
    r"(.*)(possibilities)(.*)(modulo)(.*)": "by (first | exact mod_2_poss _ | exact mod_3_poss _ | exact mod_4_poss _ | exact mod_5_poss _)",
    r"(.*)(modulo)(.*)(possibilities)(.*)": "by (first | exact mod_2_poss _ | exact mod_3_poss _ | exact mod_4_poss _ | exact mod_5_poss _)",
}


def using_theorems(theorems: list[str]) -> str:
    proof = f"repeat (first | ring | simp_all [{', '.join(theorems)}])"
    return "by \n" + indent(proof)


def induction_hypothesis(
    theorems: list[tuple[str, str, int]], **kwargs
) -> str:
    return theorems[-1][1] + " (by trivial)" * theorems[-1][2]


PARAMETRIC_PROOFS: dict[str, str] = {
    r"(.*)(induction\s*hypothesis)(.*)": induction_hypothesis,
}

DEFAULT_PROOF = "by repeat (first | trivial | ring | simp_all)"


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
            r"([Hh]ave|[Dd]erive|[Gg]ives|[Ss]how|[Pp]rove)",  # have keyword
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

        # for feedback
        self.match = match

        self.string = string
        self.left_side = match.group(1).strip(" ,.;")
        self.right_side = match.group(3).strip(" ,.;")

        self.statement = self.get_statement()
        self.proof = self.get_proof(proven_theorems)

    def get_statement(self) -> Translatable:
        for poss in POSSIBILITIES:
            try:
                return poss(self.right_side)
            except MatchingError:
                continue

        raise MatchingError(
            f"Could not find a suitable substatement for have in '{self.right_side}'.\n"
        )

    def get_proof(self, proven_theorems: list[tuple[str, str, str]]) -> str:
        # checking for previously proved theorems
        used_theorems = []
        for latex_th, lean_th, _ in proven_theorems:
            if latex_th.lower() in self.string.lower():
                used_theorems.append(lean_th)

        if used_theorems:
            # return proof
            self.proof_pattern = r"(.*)(" + "|".join(used_theorems) + r")(.*)"
            return using_theorems(used_theorems)

        for pattern, param_proof in PARAMETRIC_PROOFS.items():
            if re.fullmatch(pattern, self.string):
                self.proof_pattern = pattern
                return param_proof(theorems=proven_theorems)

        # should be proved by calc
        if (
            isinstance(self.statement, MultiplePropositions)
            and len(self.statement.propositions) == 1
            and isinstance(self.statement.propositions[0], Equation)
        ):
            self.proof_pattern = r"(.*)"
            return CALC_PROOF

        # for simple proofs
        for pattern, proof in SIMPLE_PROOFS.items():
            if re.fullmatch(pattern, self.string):
                self.proof_pattern = pattern
                return proof

        # if no proof is given
        self.proof_pattern = r"(.*)"
        return DEFAULT_PROOF

    def translate(self, hyp_name=None, **kwargs) -> str:
        if hyp_name is None:
            return self.statement.translate()

        if isinstance(self.statement, SimpleStatement):
            return self.statement.translate()

        if (
            self.proof == CALC_PROOF
            and isinstance(self.statement, MultiplePropositions)
            and len(self.statement.propositions) == 1
            and isinstance(self.statement.propositions[0], Equation)
        ):
            have = f"have {self.statement.propositions[0].translate(hyp_name=hyp_name, by_calc=True)}"
            # rw = f"try rw [{hyp_name}]"
            return have # + "\n" + rw

        return f"have {self.statement.translate(hyp_name=hyp_name, proof=self.proof)}"

    def can_create_new_goals(self) -> bool:
        return self.statement.can_create_new_goals()

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        feedback = []
        # left side (no statement, can only contain a proof)
        if match := re.fullmatch(self.proof_pattern, self.left_side):
            for i, group in enumerate(match.groups()):
                group_type = "ignored" if i % 2 == 0 else "parameter"
                feedback.append((group_type, group))
        else:
            feedback.append(("ignored", self.left_side))

        # have keyword
        feedback.append(("keyword", self.match.group(2)))

        # right side (statement)
        statement_feedback = self.statement.interpretation_feedback()

        # check each section in the statement
        for section_type, section in statement_feedback:
            # if it is ignored and we have a match for our proof pattern, we add the different parts
            if section_type == "ignored" and (
                match := re.fullmatch(self.proof_pattern, section)
            ):
                for i, group in enumerate(match.groups()):
                    group_type = "ignored" if i % 2 == 0 else "parameter"
                    feedback.append((group_type, group))
            # otherwise, we add the whole section
            else:
                feedback.append((section_type, section))

        return feedback
