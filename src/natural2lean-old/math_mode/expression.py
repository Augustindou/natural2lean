from ..structure.matching import Matching

# TODO : make the difference between ab and a * b based on the presence or not of identifiers a and b or ab before


class Expression(Matching):
    """Expression class.
    An expression is a sequence of Identifiers or numeric values separated by arithmetic operators. `natural2lean.structure.matching` contains useful information to understand the interactions between classes.

    Some examples of Expressions (that will be matched) are :
        - a + b
        - (2 + 3) * 4
        - a * b + c
        - -a
        - ...

    Some more information :
        - This class has no contents. `self.string` can be interpreted directly by `lean4`.
        - The string passed as argument to the constructor must be interpretable by `lean4`. If it is formatted for LaTex, it has to be processed by `translate_latex_math`. See `natural2lean.utils.translate_math` for more information.
        - Expressions can also be initialised directly, passing the string of its contents to the constructor (as it is done in `natural2lean.math_mode.equation`).
    """

    pattern: str = (
        # any letter, number, blank space or operator
        r"([+\-*/^%(). ]*(?:\w)+(?:\w|\s|[+\-*/^%(). ])*)"
    )

    def set_contents(self):
        self.string = self.string.strip()

    def translate(self, **kwargs) -> str:
        return self.string

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            # not considering differences between (x + y) and (x+y)
            return self.string.replace(" ", "") == other.string.replace(" ", "")
        return False
