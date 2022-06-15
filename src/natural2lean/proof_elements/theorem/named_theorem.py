import re
from .theorem import Theorem, STATEMENT_POSSIBILITIES
from ...utils.exceptions import MatchingError
from ...utils.text import subscript

space = r"\s*"



class NamedTheorem(Theorem):
    pattern: str = space.join(
        [
            "",  # ignore leading space
            r"[Tt]heorem",  # Theorem keyword
            r"(.*)",  # Theorem name
            r":",  # separation between name and statement
            r"(.*)",  # Theorem statement
            "",  # ignore trailing space
        ]
    )

    def __init__(self, string: str) -> None:
        if not (match := re.fullmatch(self.pattern, string)):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        # name
        self.latex_name = match.group(1)
        self.lean_name = self.latex_name.lower().replace(" ", "_")
        if self.lean_name[0].isdigit():
            self.lean_name = "_" + self.lean_name

        # content
        for poss in STATEMENT_POSSIBILITIES:
            try:
                self.statement = poss(match.group(2))
                self.set_hypotheses_and_theses()
                return
            except MatchingError:
                pass

        raise MatchingError(f"Could not match any statement to prove for {string}, tried {', '.join([p.__name__ for p in STATEMENT_POSSIBILITIES])}.")
        

    def translate(self, **kwargs) -> str:
        if self.hypotheses:
            lean_identifiers = self.hypotheses.translate_identifiers()
            lean_hypotheses = " ".join(
                [
                    f"(h{subscript(i)} : {h.translate()})"
                    for i, h in enumerate(self.hypotheses.get_non_identifiers())
                ]
            )
            lean_theses = self.theses.translate()
            
            return f"theorem {self.lean_name} {lean_identifiers} {lean_hypotheses} : {lean_theses} := by"
        
        else:
            lean_identifiers = self.theses.translate_identifiers()
            lean_theses = self.theses.translate_non_identifiers()
            
            return f"theorem {self.lean_name} {lean_identifiers} : {lean_theses} := by"
