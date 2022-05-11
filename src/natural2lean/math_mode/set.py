import re

from .expression import Expression
from ..utils.unfolding import unfold
from ..structure.matching import Unmatchable


class Set(Unmatchable):
    # TODO : description

    sets = {
        "ℕ": "Nat",
        "ℤ": "Int",
    }

    def set_contents(self):
        # simple set (e.g. ℕ)
        if self.string.strip() in self.sets:
            self.set = self.sets[self.string.strip()]

    def translate(self, **kwargs) -> str:
        return f"{self.set}"
