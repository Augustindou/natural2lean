from .separate_propositions import get_propositions
from ..utils.exceptions import MatchingError
from ..utils.translatable import Translatable
from ..algebra.identifiers import IdentifiersInSet


class MultiplePropositions(Translatable):
    def __init__(self, string: str, **kwargs) -> None:
        self.string = string

        self.propositions, self.used_keywords = get_propositions(string)

        if not self.propositions:
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

    def translate(
        self,
        hyp_name: str = None,
        separator: str = " ∧ ",
        proof: str = None,
        **kwargs,
    ) -> str:
        if len(self.propositions) == 1:
            return self.propositions[0].translate(
                hyp_name=hyp_name, proof=proof, **kwargs
            )

        hyp_def = f"{hyp_name} : " if hyp_name else ""
        props = separator.join([prop.translate() for prop in self.propositions])
        proof = f" := {proof}" if proof else ""

        return hyp_def + props + proof

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

    def can_create_new_goals(self) -> bool:
        return any(prop.can_create_new_goals() for prop in self.propositions)

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        if not self.used_keywords:
            return [("ignored", self.string)]
        
        # check for all keywords
        keyword_positions = []
        for kw in self.used_keywords:
            if (pos := self.string.find(kw)) != -1:
                keyword_positions.append((pos, kw))
        
        # sort by position
        keyword_positions = sorted(keyword_positions)
        
        # separate into ignored and parameters
        result = []
        current_position = 0
        
        for pos, kw in keyword_positions:
            if pos > current_position:
                result.append(("ignored", self.string[current_position:pos]))
            result.append(("parameter", kw))
            current_position = pos + len(kw)
        
        result.append(("ignored", self.string[current_position:]))
        
        return result
        
        
