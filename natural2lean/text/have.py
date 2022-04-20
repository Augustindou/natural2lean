import re

from .such_that import SuchThat
from ..math_mode.equation import Equation
from ..math_mode.math import Math
from ..propositions.implication import Implication
from ..structure.matching import Matching
from ..utils.indentation import indent


class Have(Matching):
    """Have class.
    The 'have' keyword is used to identify expressions that we want to prove.
    """

    pattern: str = r"((.*)\s*have\s*(.*))"

    def set_contents(self):
        # rematch
        match = re.fullmatch(self.pattern, self.string)
        if not match:
            raise ValueError(
                f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method."
            )

        # plain text parts
        self.left_side = match.group(2).strip(" ,.;")
        self.right_side = match.group(3).strip(" ,.;")
        # definition
        self.statement = self.get_statement()
        self.proof = self.get_proof()

    def get_statement(
        self,
        full_match_possibilities: list[Matching] = [
            Implication,
            SuchThat,
        ],
        partial_match_possibilities: list[Matching] = [
            Math,
        ],
    ):
        for possibility in full_match_possibilities:
            match = possibility.match(self.right_side)
            if match != None:
                return match

        for possibility in partial_match_possibilities:
            match = re.search(possibility.pattern, self.right_side)
            if match != None:
                return possibility.match(self.right_side[match.start() : match.end()])

        raise ValueError(
            f"Could not find a meaning for the right side of the have statement in '{self.string}'."
        )

    def get_proof(self):
        # equation
        if isinstance(self.statement, Math) and self.statement.is_equation():
            return f"by \n{indent(self.statement.content.translate_to_calc())}"

        # TODO : other cases (by definition, ...) but retrieving proofs is necessary

    def translate(self) -> str:
        # TODO : {get_hypothesis_name()}
        return f"have {self.statement.translate()} := {self.proof}"
