from .identifier import Identifier
from ..utils.unfolding import unfold
from ..structure import Matching


class MultipleIdentifiers(Matching):
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
    
    # TODO : match recursively (set_contents should match MultipleIdentifiers, then Identifier and then flatten the list)
    # MultipleIdentifiers should return identifier, identifier, identifier, ... 
    # with return identifier, next_identifiers.set_contents and then flatten the list ?
    # TODO : case with a, b \in (...)