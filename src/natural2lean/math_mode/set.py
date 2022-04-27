import re

from .expression import Expression
from ..utils.unfolding import unfold
from ..structure.matching import Unmatchable

# types


class Set(Unmatchable):
    # TODO : description
    SET = 1
    POSSIBILITIES = 2

    set_match = {
        "ℕ": "Nat",
        "ℤ": "Int",
    }

    poss_match = r"\s*__SET__\[(.+)\]\s*"
    unfold_match = (
        # opening 1st group
        r" *("
        # group for expression
        r"(" + Expression.pattern[1:-1] + r")"
        # separator (comma)
        r" *(?:(,) *"
        # group for following expressions
        r"(" + Expression.pattern[1:-1] + r"(?: *, *" + Expression.pattern[1:-1] + r")*) *)*) *"
    )

    def set_contents(self):
        self.type = None
        
        # simple set (e.g. ℕ)
        if self.string.strip() in self.set_match:
            self.type = Set.SET
            self.set = self.set_match[self.string.strip()]

        # set of possibilities ({1, 2, 3} which will have been translated into __SET__[1, 2, 3])
        if (match := re.fullmatch(self.poss_match, self.string)) is not None:
            self.type = Set.POSSIBILITIES
            elements, separators = unfold(self.unfold_match, match.group(1))
            self.set = [Expression.match(element) for element in elements]
    
    def detect_errors(self):
        if self.type is None:
            raise ValueError(f"The system does not understand the set in '{self.string}'")
        
        if self.type == Set.POSSIBILITIES:
            if any([e == None for e in self.set]):
                raise ValueError(f"The system does not understand the set in '{self.string}'")
        return super().detect_errors()

    def translate(self, identifier=None, **kwargs) -> str:
        if self.type == Set.SET:
            return f"{self.set}"
        
        if self.type == Set.POSSIBILITIES and identifier is not None:
            return " ∨ ".join([f"{identifier} = {expr.translate()}" for expr in self.set])

        raise ValueError(f"Problem translating.\n  identifier: {identifier} \n  string: {self.string}")
