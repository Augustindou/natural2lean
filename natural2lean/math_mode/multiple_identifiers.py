from __future__ import annotations
from ..utils.unfolding import unfold
from ..structure.matching import Matching
from .identifier import Identifier


class MultipleIdentifiers(Matching):
    """MultipleIdentifiers class.
    MultipleIdentifiers matches any sequence of identifiers separated by a comma. Identifiers will be available in `self.identifiers`.

    Some examples of what MultipleIdentifiers will match are :
        - a
        - a, b
        - a  ,b
        - a, b, c, d
        - ...

    Some more information :
        - TODO
    """

    #  *(([a-zA-Z]\w*) *(?:(,) *([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*) *)?) *
    pattern: str = (
        # opening group
        r" *("
        # first term (an identifier begins with a letter and can contain any number of letters, digits or underscores)
        r"([a-zA-Z]\w*)"
        # group "extension" (to allow for only 1 identifier)
        r" *(?:"
        # comma to separate
        r"(,) *"
        # second term (can contain multiple identifiers)
        r"([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*)"
        # closing groups (allow 0 or 1 "extension")
        r" *)?) *"
    )

    def set_contents(self) -> None:
        elements, separators = unfold(self.pattern, self.string)

        self.identifiers: list[Identifier] = [Identifier(e) for e in elements]

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return self.identifiers == other.identifiers
        return False

    def translate(self) -> str:
        return " ".join([i.translate() for i in self.identifiers])
