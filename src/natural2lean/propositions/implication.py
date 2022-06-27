import re
from .multiple_propositions import MultiplePropositions
from ..utils.exceptions import MatchingError
from ..utils.translatable import Translatable

space = r"\s*"
punctuation = " .,;:"


class Implication(Translatable):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"([Ii]f)",  # if keyword
            r"(.*)",  # hypotheses
            r"([Tt]hen)",  # then keyword
            r"(.*)",  # theses
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str) -> None:
        match = re.fullmatch(self.pattern, string)
        if not match:
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # for feedback
        self.match = match

        self.string = string
        self.hypotheses = MultiplePropositions(match.group(2).strip(punctuation))
        self.theses = MultiplePropositions(match.group(4).strip(punctuation))

    def translate(self, hyp_name: str = None, proof: str = None, **kwargs) -> str:
        assert (
            proof is None == hyp_name is None
        ), "Should always use proof with hyp_name."

        hyp_def = f"{hyp_name} : " if hyp_name else ""
        proof = f" := {proof}" if proof else ""

        hypotheses_tr = self.hypotheses.translate(separator=" → ")
        theses_tr = self.theses.translate()

        implication = f"{hypotheses_tr} → {theses_tr}"

        return hyp_def + implication + proof

    def interpretation_feedback(self) -> list[tuple[str, str]]:
        return [
            ("keyword", self.match.group(1)),
            *self.hypotheses.interpretation_feedback(),
            ("keyword", self.match.group(3)),
            *self.theses.interpretation_feedback(),
        ]
