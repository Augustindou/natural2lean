import re

from .such_that import SuchThat
from ..math_mode.equation import Equation
from ..math_mode.math import Math
from ..propositions.implication import Implication
from ..propositions.multiple_propositions import MultiplePropositions
from ..structure.matching import Matching, Unmatchable
from ..utils.indentation import indent

# simple statements (contradiction, ...)
SIMPLE_STATEMENTS = {
    "contradiction": "contradiction",
}


class Have(Matching):
    """Have class.
    The 'have' keyword is used to identify expressions that we want to prove.
    """

    pattern: str = r"((.*)\s*have\s*(.*))\s*"

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
    ):
        full_match_possibilities: list[Matching] = [
            Implication,
            SuchThat,
        ]

        for possibility in full_match_possibilities:
            match = possibility.match(self.right_side)
            if match != None:
                return match

        # match math mode
        match = re.search(Math.pattern, self.right_side)
        if match != None:
            math_match: Math = Math.match(self.right_side[match.start() : match.end()])
            if math_match.is_equation() or math_match.is_identifiers_in_set() or math_match.is_expression_possibilities():
                return math_match

        # multiple propositions
        try:
            return MultiplePropositions(self.right_side)
        except ValueError:
            pass

        # for the simple cases (we have a contradiction)
        for statement in SIMPLE_STATEMENTS:
            if statement in self.right_side:
                return statement
        
        raise ValueError(
            f"Could not find a meaning for the right side of the have statement in '{self.string}'."
        )

    def get_proof(self):
        # equation
        if isinstance(self.statement, Math) and self.statement.is_equation():
            return f"by \n{indent(self.statement.content.translate_to_calc())}"

        if "definition" in self.string.lower():
            proof = "simp at *\nassumption\n"
            return f"by \n{indent(proof)}"
        
        if "possibilities" in self.string.lower() and "modulo" in self.string.lower():
            return f"mod_3_poss _"

        # if no proof is given, just use simp [*]
        return "simp [*]"


    def translate(self, hyp="h", **kwargs) -> str:
        
        # for the simple cases (we have a contradiction)
        if isinstance(self.statement, str) and self.statement in SIMPLE_STATEMENTS:
            return SIMPLE_STATEMENTS[self.statement]
        
        return f"have {self.statement.translate(hyp=hyp)} := {self.proof}\n"
