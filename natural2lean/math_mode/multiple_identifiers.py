from ..structure import Matching


class MultipleIdentifiers(Matching):
    pattern = (
        # opening group
        r"( *"
        # first term (an identifier begins with a letter and can contain any number of letters, digits or underscores)
        r"([a-zA-Z]\w*)"
        # comma to separate
        r" *(,) *"
        # second term (can contain multiple identifiers)
        r"([a-zA-Z]\w*(?: *, *[a-zA-Z]\w*)*)"
        # closing group
        r" *)"
    )
    
    # TODO : match recursively (set_contents should match MultipleIdentifiers, then Identifier and then flatten the list)
    # MultipleIdentifiers should return identifier, identifier, identifier, ... 
    # with return identifier, next_identifiers.set_contents and then flatten the list ?
    # TODO : case with a, b \in (...)