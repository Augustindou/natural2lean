from __future__ import annotations

from ..structure import Matching
from .translate_math import Latex2LeanMath
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

    pattern: str = r" *\${1,2} *(.+?) *\${1,2} *"

    def __init__(self, string: str) -> None:
        super().__init__(Latex2LeanMath(string).result())

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

        raise ValueError(
            f"No match found for {self.string}, tested {', '.join([poss.__name__ for poss in possible_subtypes])}"
        )

    def translate(self) -> str:
        raise NotImplementedError


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
