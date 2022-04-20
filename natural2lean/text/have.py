import re
from ..structure.matching import Matching


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

        # definition
        self.right_side = match.group(3).strip(" ,.;")
        # proof
        # TODO get access to hypothesis
        self.proof = match.group(2).strip(" ,.;") 
