import re
from .multiple_identifiers import MultipleIdentifiers
from .set import Set
from ..structure.matching import Matching

# TODO : case for $ a \in \{1, 2, 3\} $


class IdentifiersInSet(Matching):
    """IdentifiersInSet class.
    Variation of the MultipleIdentifiers, allows to match identifiers as part of a set. Identifiers will be available in `self.identifiers`.

    Some examples of what IdentifiersInSet will match are :
        - a ∈ __SET__[1, 2, 3]
        - a, b ∈ ℕ
        - a, b, c, d ∈ ℤ
        - ...

    Some more information :
        - The intermediate representation (a, b ∈ ℕ) can be obtained by applying `natural2lean.utils.translate_math.translate_latex_math()` to the latex string (a, b \\in \\mathbb{N}).
    """

    #  *((([a-zA-Z]\w*) *(?:(,) *([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*) *)?) *(∈) *(\S+.*?)) *
    pattern: str = (
        # open group
        r" *("
        # same as MultipleIdentifiers
        r"(([a-zA-Z]\w*) *(?:(,) *([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*) *)?) *"
        # # match keyword for inclusion (can be adapted / extended for other notations)
        r"(∈) *"
        # the set
        r"(\S+.*?)"
        # # closing group
        r") *"
    )

    def set_contents(self) -> None:
        match = re.fullmatch(self.pattern, self.string)

        # set
        self.relation_to_set = match.group(6).strip()
        self.set = Set(match.group(7).strip())

        # unfold the elements
        self.identifiers = MultipleIdentifiers(match.group(2)).identifiers

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return (
                self.identifiers == other.identifiers
                and self.relation_to_set == other.relation_to_set
                and self.set == other.set
            )
        return False

    def translate(self) -> str:
        lean_identifiers = " ".join(
            identifier.translate() for identifier in self.identifiers
        )
        lean_set = self.set.translate()
        return f"({lean_identifiers} : {lean_set})"
