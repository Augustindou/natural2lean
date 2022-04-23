from ..structure.matching import Unmatchable

# TODO : case for $ a \in \{1, 2, 3\} $


class Set(Unmatchable):
    # TODO : description

    sets = {
        "ℕ": "Nat",
        "ℤ": "Int",
    }

    def detect_errors(self):
        if self.string not in self.sets:
            raise ValueError(f"The system does not understand the set {self.string}")
        return super().detect_errors()

    def translate(self) -> str:
        return self.sets[self.string]
