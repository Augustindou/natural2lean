from ...utils.translatable import Translatable
from ...propositions.multiple_propositions import MultiplePropositions
from ...propositions.implication import Implication

STATEMENT_POSSIBILITIES = [Implication, MultiplePropositions]


class Theorem(Translatable):
    def __init__(self):
        self.statement: Translatable = None
        raise NotImplementedError

    def set_hypotheses_and_theses(self):
        if isinstance(self.statement, Implication):
            self.hypotheses = self.statement.hypotheses
            self.theses = self.statement.theses
        elif isinstance(self.statement, MultiplePropositions):
            self.hypotheses = None
            self.theses = self.statement