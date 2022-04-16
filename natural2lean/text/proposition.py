from __future__ import annotations
import re

from ..math_mode.math import Math
from ..structure.matching import Unmatchable


# TODO : Extend to support multiple argument functions


class Proposition(Unmatchable):
    """Proposition class.
    Not matchable, should only be initialized with the constructor.
    """

    def set_contents(self):
        math_match: Math = Math.match(self.string)
        # identifier definition
        if math_match != None and math_match.is_identifiers_in_set():
            self.function = "IDENTIFIER_DEFINITION"
            self.content = math_match.content
            return
        # equation
        if math_match != None and math_match.is_equation():
            self.function = "EQUATION"
            self.content = math_match.content
            return
        if math_match != None:
            raise ValueError(
                f"{self.string} is fully matched by Math but cannot find what it is."
            )

        # function (pattern matches directly what is returned by separate_propositions, hence it is a bit specific)
        pattern = "(.+) \$ (.+) \$"
        function_match = re.fullmatch(pattern, self.string)
        self.function = function_match.group(1)
        self.content = Math.match(f"$ {function_match.group(2)} $")

    def translate(self) -> str:
        if self.function == "IDENTIFIER_DEFINITION":
            return f"({self.content.translate()})"
        if self.function == "EQUATION":
            return f"({self.content.translate()})"
        return f"{self.function} ({self.content.translate()})"

    def is_identifier_definition(self):
        return self.function == "IDENTIFIER_DEFINITION"
