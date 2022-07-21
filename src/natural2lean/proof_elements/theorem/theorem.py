from ...utils.translatable import Translatable
from ...propositions.multiple_propositions import MultiplePropositions
from ...propositions.implication import Implication
from ...utils.text import subscript

STATEMENT_POSSIBILITIES = [Implication, MultiplePropositions]


class Theorem(Translatable):
    def __init__(self):
        self.statement: Translatable = None
        self.latex_name: str = None
        self.lean_name: str = None
        self.n_args: int = None
        raise NotImplementedError

    def set_hypotheses_and_theses(self):
        if isinstance(self.statement, Implication):
            self.hypotheses = self.statement.hypotheses
            self.theses = self.statement.theses
            self.n_args = len(self.hypotheses.propositions)
        elif isinstance(self.statement, MultiplePropositions):
            self.hypotheses = None
            self.theses = self.statement
            self.n_args = len(self.theses.get_identifiers())

    def translate(self, **kwargs) -> str:
        if self.hypotheses:
            lean_identifiers = self.hypotheses.translate_identifiers()
            lean_hypotheses = " ".join(
                [
                    f"(h{subscript(i)} : {h.translate()})"
                    for i, h in enumerate(self.hypotheses.get_non_identifiers())
                ]
            )
            lean_theses = self.theses.translate()

            return f"theorem {self.lean_name} {lean_identifiers} {lean_hypotheses} : {lean_theses} := by"

        else:
            lean_identifiers = self.theses.translate_identifiers()
            lean_theses = self.theses.translate_non_identifiers()

            return f"theorem {self.lean_name} {lean_identifiers} : {lean_theses} := by"
