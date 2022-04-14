from ast import pattern
import re
from ..text.implication import Implication
from .matching import Matching


class Theorem(Matching):
    # ([Tt]heorem\s*(.*):\s*((?:.|\s)*?))\n\s*?\n\s*
    pattern: str = (
        # opening group
        r"("
        # Theorem keyword
        r"[Tt]heorem\s*"
        # Theorem name
        r"(.*)"
        # ':' for separation
        r":\s*"
        # theorem statement
        r"((?:.|\s)*?))"
        # blank line between theorem and proof
        r"\n\s*?\n\s*"
    )
    
    def set_contents(self):
        match = re.fullmatch(self.pattern, self.string)
        if match == None:
            raise ValueError(f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method.")

        # name
        self.latex_name = match.group(2)
        self.lean_name = self.latex_name.replace(" ", "_")
        if self.lean_name[0].isdigit():
            self.lean_name = "_" + self.lean_name
        
        # content
        self.statement = Implication.match(match.group(3))
