from ..structure.matching import Unmatchable
from ..utils.separate_propositions import separate_propositions
from .proposition import Proposition


class MultiplePropositions(Unmatchable):
    """MultiplePropositions class.
    MultiplePropositions matches anything. This class should only be used when it is known that the string contains one or more propositions. The different propositions will be identified in `natural2lean.utils.separate_propositions` and the result will be stored in the `propositions` attribute.

    Some examples of what MultiplePropositions will match are :
        - this is a proposition
        - hello world
        - $a \in \mathbb{N}$ is even and $a^2$ is even

    Some more information :
        - TODO
    """

    pattern: str = None

    def set_contents(self):
        self.propositions = [
            Proposition(prop) for prop in separate_propositions(self.string)
        ]
