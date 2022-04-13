from __future__ import annotations

from ..structure import Matching
from .translate_math import Latex2LeanMath
from .equation import Equation
from .expression import Expression
from .multiple_identifiers import MultipleIdentifiers
import re

# TODO : either ' $ [...] $ ' or ' $$ [...] $$ ', but not ' $ [...] $$ '

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

    def set_contents(self) -> None:
        # match for equation
        equation = Equation.match(self.string)
        if equation != None:
            self.content = equation
            return
        
        # match for expression
        expression = Expression.match(self.string)
        if expression != None:
            self.content = expression
            return
        
        # match for identifiers
        identifiers = MultipleIdentifiers.match(self.string)
        if identifiers != None:
            self.content = identifiers
            return
        
        raise ValueError(f"No match found for {self.string}")

    def translate(self) -> str:
        raise NotImplementedError


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
