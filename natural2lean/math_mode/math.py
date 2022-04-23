from __future__ import annotations

from ..structure.matching import Matching
from ..utils.translate_math import translate_latex_math
from .equation import Equation
from .expression import Expression
from .multiple_identifiers import MultipleIdentifiers
from .identifiers_in_set import IdentifiersInSet
import re


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
            # order matters here ! Expression matches almost anything
            MultipleIdentifiers,
            IdentifiersInSet,
            Equation,
            Expression,
        ]
        # rematch
        match = re.fullmatch(self.pattern, self.string)
        if match == None:
            raise ValueError(f"'{self.string}' is not a valid math block.")

        # different strings
        self.latex_string = match.group(2)
        self.lean_string = translate_latex_math(self.latex_string)

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

    def translate(self, **kwargs) -> str:
        return self.content.translate(**kwargs)

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return self.content == other.content
        return False

    def is_equation(self):
        return isinstance(self.content, Equation)

    def is_expression(self):
        return isinstance(self.content, Expression)

    def is_multiple_identifiers(self):
        return isinstance(self.content, MultipleIdentifiers)

    def is_identifiers_in_set(self):
        return isinstance(self.content, IdentifiersInSet)


# TODO : x = ab => x = a * b or x = ab (as a single identifier) => dependent on the presence or not of identifiers a and b or ab before
