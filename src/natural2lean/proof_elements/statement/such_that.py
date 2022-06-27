import re
from .statement import Statement
from ...propositions.multiple_propositions import MultiplePropositions
from ...algebra.identifiers import Identifier
from ...utils.exceptions import MatchingError, TranslationError


space = r"\s*"


class SuchThat(Statement):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"(.*)",  # left side
            r"([Ss]uch)",  # such that keyword
            r"([Tt]hat)",  # with space between
            r"(.*)",  # right side
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string, **kwargs) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # for feedback
        self.match = match

        # identifiers
        self.identifiers = MultiplePropositions(match.group(1))

        if len(self.identifiers.get_identifiers()) == 0:
            raise TranslationError(
                f"Found no identifiers before 'such that' in '{string}'.\n"
            )

        if len(self.identifiers.get_non_identifiers()) > 0:
            raise TranslationError(
                f"A proposition before 'such that' in '{string}' is not an identifier definition.\n"
            )

        # hypotheses
        self.hypotheses = MultiplePropositions(match.group(4))

    def translate(self, hyp_name=None, proof=None, **kwargs) -> str:
        assert (proof is None) == (
            hyp_name is None
        ), "Should always use proof with hyp_name."

        identifiers: list[Identifier] = []
        for ident_in_set in self.identifiers.get_identifiers():
            identifiers += ident_in_set.identifiers

        id_names = [i.translate() for i in identifiers]
        id_defs = " ".join(
            [idents.translate() for idents in self.identifiers.get_identifiers()]
        )
        hyp_def = self.hypotheses.translate()

        constructor = f"⟨{', '.join(id_names)}, {hyp_name}⟩"
        exists = f"∃ {id_defs}, {hyp_def}"

        return f"{constructor} : {exists} := {proof}"

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        feedback = [
            ("keyword", self.match.group(2)),
            ("keyword", self.match.group(3)),
        ]

        return (
            self.identifiers.interpretation_feedback()
            + feedback
            + self.hypotheses.interpretation_feedback()
        )
