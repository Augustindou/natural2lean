from __future__ import annotations
from ..structure import Matching
from .translate_math import Latex2LeanMath
import re


class Math(Matching):
    """Math block
    @attribute __pattern: str, matches strings of the form ' $ [...] $ ' and ' $$ [...] $$ '"""

    __pattern: str = r" *\${1,2} *(.+?) *\${1,2} *"

    def __init__(self, string: str) -> None:
        super().__init__(Latex2LeanMath(string).result())

    def __get_contents(self) -> None:
        self.contents = []
        # check whether equation
        # check whether expression
        # check whether identifier
        raise NotImplementedError

    def translate(self) -> str:
        raise NotImplementedError

        # TODO : further recursive matching


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
