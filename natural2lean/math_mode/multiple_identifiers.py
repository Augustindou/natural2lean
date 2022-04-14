from .identifier import Identifier
from ..utils.unfolding import unfold
from ..structure import Matching
import re


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

    pattern: str = (
        # opening group
        r"( *"
        # first term (an identifier begins with a letter and can contain any number of letters, digits or underscores)
        r"([a-zA-Z]\w*)"
        # allow for no second group (only 1 identifier)
        r" *(?:"
        # comma to separate
        r"(,) *"
        # second term (can contain multiple identifiers)
        r"([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*)"
        # closing groups (1st and non-capturing group if only 1 identifier)
        r" *)*)"
    )

    def set_contents(self) -> None:
        elements, separators = unfold(self.pattern, self.string)

        self.identifiers: list[Identifier] = [Identifier(e) for e in elements]


class IdentifiersInSet(MultipleIdentifiers):
    """IdentifiersInSet class.
    Variation of the MultipleIdentifiers, allows to match identifiers as part of a set. Identifiers will be available in `self.identifiers`.

    Some examples of what IdentifiersInSet will match are :
        - a \\in {a, b}
        - a, b \\in \mathbb{N}
        - a, b, c, d \\in \mathbb{Z}
        - ...

    Some more information :
        - TODO
    """

    pattern: str = (
        # same as MultipleIdentifiers
        r"( *(([a-zA-Z]\w*) *(?:(,) *([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*) *))"
        # match keyword for inclusion (can be adapted / extended for other notations)
        r"(∈)"
        # the set
        r"(.*)"
        # closing group
        r" *)"
    )

    def set_contents(self) -> None:
        match = re.fullmatch(self.pattern, self.string)
        
        # related to set
        self.relation_to_set = match.group(6).strip()
        self.set = match.group(7).strip() # TODO : Set class
        
        # unfold the elements
        self.identifiers = MultipleIdentifiers(match.group(2)).identifiers