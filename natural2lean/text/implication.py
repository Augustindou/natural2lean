import re

from natural2lean.text.multiple_propositions import MultiplePropostions
from ..structure.matching import Matching


class Implication(Matching):
    # \s*([Ii]f\s*(.*)\s*then\s*(.*))\s*
    pattern: str = (
        # start group
        r"\s*("
        # if keyword
        r"[Ii]f\s*"
        # hypotheses
        r"(.*)"
        # then keyword
        r"\s*then\s*"
        # theses
        r"(.*)"
        # end group
        r")\s*"
    )

    def set_contents(self):
        match = re.fullmatch(self.pattern, self.string)
        if not match:
            raise ValueError(
                f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method."
            )

        # hypotheses
        self.hypotheses = MultiplePropostions(match.group(2))
        # theses (can be multiple)
        self.theses = MultiplePropostions(match.group(3))


# if $m \in \mathbb{N}$ is even, then $m^2$ is even.
