from __future__ import annotations

from ..structure.matching import Matching
from ..utils.translate_math import translate_latex_math
from .equation import Equation
from .expression import Expression
from .multiple_identifiers import MultipleIdentifiers, IdentifiersInSet
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

    pattern: str = r"\s*(\${1,2}\s*(.+?)\s*\${1,2})\s*"

    def set_contents(self) -> None:
        possible_subtypes: tuple[type[Matching]] = [
            Equation,
            Expression,
            MultipleIdentifiers,
            IdentifiersInSet,
        ]
        # rematch
        match = re.fullmatch(self.pattern, self.string)
        if match == None:
            raise ValueError(f"'{self.string}' is not a valid math block.")

        # translate to math understandable by lean
        self.lean_string = translate_latex_math(match.group(2))

        # subtypes
        for poss in possible_subtypes:
            content = poss.match(self.lean_string)
            if content != None:
                self.content: Matching = content
                return

        raise ValueError(
            f"No match found for {self.lean_string}, tested {', '.join([poss.__name__ for poss in possible_subtypes])}"
        )

    def detect_errors(self):
        # different number of $ on each side
        if self.string.count("$") % 2 == 1:
            raise ValueError(
                f"Number of dollar signs on left and right side should be equal, but found different in {self.string}."
            )

    def translate(self) -> str:
        return self.content.translate()

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return self.content == other.content
        return False


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
