from __future__ import annotations

from ..structure.matching import Matching
from ..utils.translate_math import translate_latex_math
from .equation import Equation
from .expression import Expression
from .multiple_identifiers import MultipleIdentifiers
import re

# TODO : either ' $ [...] $ ' or ' $$ [...] $$ ', but not ' $ [...] $$ ' (not useful for proof of concept)


class Math(Matching):
    """Math class.
    A Math block is anything that's in math mode in LaTeX. `natural2lean.structure.matching` contains useful information to understand the interactions between classes.

    Some examples of Expressions (that will be matched) are :
        - $a + b$
        - $$a + b = 3$$
        - $a, b \\in \\mathbb{R}$
        - $ a + b $$ (this one will be matched but is not valid in LaTeX)
        - ...

    Some more information :
        - TODO
    """

    pattern: str = r"\s*\${1,2}\s*(.+?)\s*\${1,2}\s*"

    def __init__(self, string: str) -> None:
        super().__init__(translate_latex_math(string))

    def set_contents(
        self,
        possible_subtypes: tuple[type] = (
            Equation,
            Expression,
            MultipleIdentifiers,
        ),
    ) -> None:
        for poss in possible_subtypes:
            content = poss.match(self.string)
            if content != None:
                self.content = content
                return

        raise ValueError(
            f"No match found for {self.string}, tested {', '.join([poss.__name__ for poss in possible_subtypes])}"
        )

    def translate(self) -> str:
        raise NotImplementedError

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return self.content == other.content
        return False


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
