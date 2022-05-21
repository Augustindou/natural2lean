import re
from natural2lean.proof_elements.propositions.multiple_propositions import (
    MultiplePropositions,
)
from .statement import Statement
from ..propositions.separate_propositions import get_propositions
from ...algebra.identifiers import Identifier, IdentifiersInSet
from ...utils.exceptions import MatchingError, TranslationError


space = r"\s*"


class SuchThat(Statement):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"(.*)",  # left side
            r"[Ss]uch",  # such that keyword
            r"[Tt]hat",  # with space between
            r"(.*)",  # right side
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # identifiers
        props = MultiplePropositions(match.group(1))
        self.identifiers = props.get_identifiers()

        if len(self.identifiers) == 0:
            raise TranslationError(
                f"Found no identifiers before 'such that' in '{string}'."
            )

        if len(props.get_non_identifiers()) > 0:
            raise TranslationError(
                f"A proposition before 'such that' in '{string}' is not an identifier definition."
            )

        # hypotheses
        self.hypotheses = MultiplePropositions(match.group(2))

    def translate(self, hyp_name=None, proof=None, **kwargs) -> str:
        assert (proof is None) == (
            hyp_name is None
        ), "Should always use proof with hyp_name."

        identifiers: list[Identifier] = []
        for ident_in_set in self.identifiers:
            identifiers += ident_in_set.identifiers

        id_names = [i.translate() for i in identifiers]
        id_defs = " ".join([idents.translate() for idents in self.identifiers])
        hyp_def = self.hypotheses.translate()

        constructor = f"⟨{', '.join(id_names)}, {hyp_name}⟩"
        exists = f"∃ {id_defs}, {hyp_def}"

        return f"{constructor} : {exists} := {proof}"
