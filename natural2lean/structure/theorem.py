import re
from ..propositions.implication import Implication
from .matching import Matching
from ..utils.indentation import indent


# TODO : Modify Theorem to match with 'lemma' or 'theorem' keywords (or others ?).
# TODO : Modify Theorem to possibly match just a proposition, not necessarily an implication.


class Theorem(Matching):
    """Theorem class.
    Theorem matches needs the "theorem" keyword, followed by a name, followed by the content of the theorem (an implication).

    Some examples of what MultipleIdentifiers will match are :
        - a
        - a, b
        - a  ,b
        - a, b, c, d
        - ...

    Some more information :
        - TODO
    """

    # ([Tt]heorem\s*(.*):\s*((?:.|\s)*?))\s*(?:\n\s*\n\s*(?:.|\s)*|$)
    pattern: str = (
        # Theorem keyword
        r"([Tt]heorem\s*"
        # Theorem name
        r"(.*)"
        # ":"
        r":\s*"
        # Theorem statement (lazy matching to avoid matching the proof with it)
        r"((?:.|\s)*?))"
        # avoid extra blanks
        r"\s*"
        # group 2 possibilities : only theorem or theorem with proof
        r"(?:"
        # theroem with proof : proof must be separated by a blank line
        r"\n\s*\n\s*"
        # proof contents
        r"(?:.|\s)*"
        # if only theorem : end of string
        r"|$)"
    )

    def set_contents(self):
        match = re.fullmatch(self.pattern, self.string)
        if not match:
            raise ValueError(
                f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method."
            )

        # name
        self.latex_name = match.group(2)
        self.lean_name = self.latex_name.lower().replace(" ", "_")
        if self.lean_name[0].isdigit():
            self.lean_name = "_" + self.lean_name

        # content
        self.statement: Implication = Implication.match(match.group(3))
        if self.statement is None:
            raise ValueError(f"Could not match an Implication in {match.group(3)}.")

    def detect_errors(self):
        if self.statement.theses.contains_identifier():
            raise ValueError(
                f"The thesis of the theorem {self.latex_name} contains an identifier. Complete statement : {self.string}"
            )
        return super().detect_errors()

    def translate(self) -> str:
        hypotheses = self.statement.hypotheses
        theses = self.statement.theses
        # translate identifiers
        lean_identifiers = hypotheses.translate_identifiers()
        # translate other hypotheses
        lean_hypotheses = hypotheses.translate_non_identifiers(separator=" → ")
        # translate theses
        lean_theses = theses.translate()

        # full statement
        theorem_statement = f"theorem {self.lean_name} {lean_identifiers} : {lean_hypotheses} → {lean_theses}"
        # introduction of hypothesis
        hyp = " ".join([f"h{i}" for i in range(len(hypotheses.get_non_identifiers()))])
        hyp_intro = f"intros {hyp}"
        return f"{theorem_statement} := by\n{indent(hyp_intro)}\n"
