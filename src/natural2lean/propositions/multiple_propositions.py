from natural2lean.math_mode.identifiers_in_set import IdentifiersInSet
from ..structure.matching import Translatable, Unmatchable
from ..utils.separate_propositions import get_propositions


class MultiplePropositions(Unmatchable):
    """MultiplePropositions class.
    MultiplePropositions matches anything. This class should only be used when it is known that the string contains one or more propositions. The different propositions will be identified in `natural2lean.utils.separate_propositions` and the result will be stored in the `propositions` attribute.

    Some examples of what MultiplePropositions will match are :
        - this is a proposition
        - hello world
        - $a \\in \\mathbb{N}$ is even and $a^2$ is even

    Some more information :
        - TODO
    """

    pattern: str = None

    def set_contents(self):
        self.propositions = get_propositions(self.string)

    def detect_errors(self):
        if len(self.propositions) == 0:
            raise ValueError("No proposition found.")
        return super().detect_errors()

    def translate(self, hyp=None, separator: str = " ∧ ") -> str:
        hyp_ident = "" if hyp is None else f" {hyp} : "
        return separator.join([prop.translate() for prop in self.propositions])

    def translate_identifiers(self, separator: str = " ") -> str:
        return separator.join([prop.translate() for prop in self.get_identifiers()])

    def get_identifiers(self) -> list[Translatable]:
        return [
            prop for prop in self.propositions if isinstance(prop, IdentifiersInSet)
        ]

    def translate_non_identifiers(self, separator: str = " ∧ ") -> str:
        return separator.join([prop.translate() for prop in self.get_non_identifiers()])

    def get_non_identifiers(self) -> list[Translatable]:
        return [
            prop for prop in self.propositions if not isinstance(prop, IdentifiersInSet)
        ]

    def contains_identifier(self) -> bool:
        return any(isinstance(prop, IdentifiersInSet) for prop in self.propositions)
