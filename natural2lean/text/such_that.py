import re
from ..propositions.multiple_propositions import MultiplePropositions
from ..propositions.proposition import Proposition
from ..utils.separate_propositions import get_propositions
from ..structure.matching import Matching


class SuchThat(Matching):
    """SuchThat class.
    x such that h is used to convey ∃ x: h
    """

    pattern: str = r"((.*)\s*such that\s*(.*))"

    def set_contents(self):
        # rematch
        match = re.fullmatch(self.pattern, self.string)
        if not match:
            raise ValueError(
                f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method."
            )

        # identifier
        propositions: list[Proposition] = [
            get_propositions(match.group(2).strip(" ,.;"))
        ]
        if len(propositions) != 1:
            raise ValueError(
                f"Found {len(propositions)} propositions before 'such that' in {self.string}, should only be one identifier definition."
            )
        self.identifier = propositions[0]

        # hypotheses
        self.hypotheses = MultiplePropositions(match.group(3).strip(" ,.;"))

    def detect_errors(self):
        if not self.identifier.is_identifier_definition():
            raise ValueError(
                f"The proposition before 'such that' in {self.string} is not an identifier definition."
            )
        return super().detect_errors()

    def translate(self, hyp_name: str = "h") -> str:
        return f"⟨{self.identifier.translate()}, ({hyp_name} : {self.hypotheses.translate()})⟩"
