import re

from ..math_mode.identifiers_in_set import IdentifiersInSet
from ..propositions.multiple_propositions import MultiplePropositions
from ..utils.separate_propositions import get_propositions
from ..structure.matching import Matching, Translatable


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
        propositions: list[Translatable] = get_propositions(
            match.group(2).strip(" ,.;")
        )
        if len(propositions) != 1:
            raise ValueError(
                f"Found {len(propositions)} propositions before 'such that' in {self.string}, should only be one identifier definition."
            )
        self.identifiers: IdentifiersInSet = propositions[0]

        # hypotheses
        self.hypotheses = MultiplePropositions(match.group(3).strip(" ,.;"))

    def detect_errors(self):
        if not isinstance(self.identifiers, IdentifiersInSet):
            raise ValueError(
                f"The proposition before 'such that' in {self.string} is not an identifier definition."
            )
        return super().detect_errors()

    def translate(self, hyp="h") -> str:
        id_names = [i.translate() for i in self.identifiers.identifiers]
        id_def = self.identifiers.translate()
        hyp_def = self.hypotheses.translate()
        return f"⟨{', '.join(id_names)}, {hyp}⟩ : ∃ {id_def}, {hyp_def}"
