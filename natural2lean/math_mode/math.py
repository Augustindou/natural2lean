from __future__ import annotations
from natural2lean.structure import Matching
from natural2lean.math_mode import Latex2LeanMath
import re


class Math(Matching):
    """Math block
    @attribute __pattern: str, matches strings of the form ' $ [...] $ '"""

    __pattern: str = r" *\$ *(.+?) *\$ *"

    def __init__(self, string: str) -> None:
        self.string = Latex2LeanMath(string).result()
        # check whether equation
        # check whether expression
        # check whether identifier
        
        # TODO : further recursive matching









# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
