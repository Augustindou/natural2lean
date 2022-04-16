from __future__ import annotations
from ..structure.matching import Matching


class Proposition(Matching):
    """Proposition class.
    Not matchable, should only be initialized with the constructor.
    """

    def set_contents(self):
        # TODO
        # identifier_definitions
        # propositions

        # only IdentifierInSet (math_mode) ($ a \in \mathbb{N} $)
        # multiple identifiers ($ a, b $)
        # identifier in set ($a$ is a natural)
        pass

    # TODO : translate to lean

    # TODO : is_identifier_definition
