import re
from .multiple_identifiers import MultipleIdentifiers
from .set import Set
from .expression import Expression
from ..structure.matching import Matching


class ExpressionPossibilities(Matching):
    """ExpressionPossibilities class.
    
        - a ∈ __SET__[1, 2, 3]
        - a + b ∈ __SET__[1, 2, 3]
        - ...
    """

    #   *(([+\-*/^%(). ]*(?:\w)+(?:\w|\s|[+\-*/^%(). ])*) *(∈) *(__SET__\[.*\])) *
    pattern: str = (
        # opening group
        r" *("
        # expression
        r"" + Expression.pattern + r""
        # in specific set
        r"*(∈) *(__SET__\[.*\])) *"
    )

    def set_contents(self) -> None:
        match = re.fullmatch(self.pattern, self.string)

        # set
        self.relation_to_set = match.group(3).strip()
        self.set = Set(match.group(4).strip())

        # match the expression
        self.expression = Expression(match.group(2))
        

    def translate(self, hyp=None, **kwargs) -> str:
        definition = "" if hyp is None else f"{hyp} : "
        
        if self.set.type == Set.POSSIBILITIES:
            return f"{definition}{self.set.translate(identifier=self.expression.translate())}"
        
        raise Exception(f"Should not happen: {self.string}, {self.__class__.__name__}")
