from ..structure import Matching


class MultipleIdentifiers(Matching):
    __pattern = (
        # start of group
        r"( *" 
        # 1st identifier, in group 2
        r"([a-zA-Z]\w*)" 
        # following identifier(s), in group 3 (begins with comma)
        r"*((?:, *[a-zA-Z]\w* *)+)" 
        # end of group
        r")" 
    )
    
    pass
    # TODO : match recursively (__get_contents should match MultipleIdentifiers, then Identifier and then flatten the list)
    # MultipleIdentifiers should return identifier, identifier, identifier, ... 
    # with return identifier, next_identifiers.__get_contents and then flatten the list ?
    # TODO : case with a, b \in (...)