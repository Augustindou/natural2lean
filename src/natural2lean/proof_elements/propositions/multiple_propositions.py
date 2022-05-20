from .separate_propositions import get_propositions
from ...utils.exceptions import MatchingError
from ...utils.translatable import Translatable
from ...algebra.identifiers import IdentifiersInSet


class MultiplePropositions(Translatable):
    def __init__(self, string: str) -> None:
        self.propositions = get_propositions(string)

        if not self.propositions:
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

    def translate(self, hyp_name=None, separator: str = " ∧ ", **kwargs) -> str:
        hyp_def = f"{hyp_name} : " if hyp_name else ""
        props = separator.join([prop.translate() for prop in self.propositions])

        return hyp_def + props

    def get_identifiers(self) -> list[IdentifiersInSet]:
        return [
            prop for prop in self.propositions if isinstance(prop, IdentifiersInSet)
        ]

    def get_non_identifiers(self) -> list[Translatable]:
        return [
            prop for prop in self.propositions if not isinstance(prop, IdentifiersInSet)
        ]
        
    def translate_identifiers(self, separator: str = " ") -> str:
        return separator.join([prop.translate() for prop in self.get_identifiers()])
    
    def translate_non_identifiers(self, separator: str = " ∧ ") -> str:
        return separator.join([prop.translate() for prop in self.get_non_identifiers()])
