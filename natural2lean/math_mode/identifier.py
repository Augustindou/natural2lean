from ..structure import Matching


class Identifier(Matching):
    """Just an identifier without operator"""

    pattern: str = r" *([a-zA-Z]\w*) *"
    
    
    # TODO : case with a \in (...)
