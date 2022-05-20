import re

from ..utils.exceptions import TranslationError

from ..propositions.implication import Implication
from ..structure.matching import Matching
from ..utils.pretty_printing import to_indices


# TODO : Modify Theorem to match with 'lemma' or 'theorem' keywords (or others ?).
# TODO : Modify Theorem to possibly match just a proposition, not necessarily an implication.


class Theorem(Matching):
    """Theorem class.
    Theorem matches needs the "theorem" keyword, followed by a name, followed by the content of the theorem (an implication).

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
        # theorem with proof : proof must be separated by a blank line
        r"\n\s*\n\s*"
        # proof contents
        r"(?:.|\s)*"
        # if only theorem : end of string
        r"|$)"
    )

    def set_contents(self):
        match = re.fullmatch(self.pattern, self.string)
        if not match:
            raise TranslationError(
                f"Could not match {self.string} in {self.__class__.__name__}, should not use __init__ directly, but create instances using the match() method."
            )

        # name
        self.latex_name = match.group(2)
        # (avoid "" and None for latex_name)
        if self.latex_name:
            self.lean_name = self.latex_name.lower().replace(" ", "_")
            if self.lean_name[0].isdigit():
                self.lean_name = "_" + self.lean_name

        # content
        self.statement: Implication = Implication.match(match.group(3))
        if self.statement is None:
            raise TranslationError(f"Could not match an Implication in {match.group(3)}.")

    def detect_errors(self):
        if self.statement.theses.contains_identifier():
            raise TranslationError(
                f"The thesis of the theorem {self.latex_name} contains an identifier. Complete statement : {self.string}"
            )
        return super().detect_errors()

    def translate(self, **kwargs) -> str:
        hypotheses = self.statement.hypotheses
        theses = self.statement.theses
        # translate identifiers
        lean_identifiers = hypotheses.translate_identifiers()
        # translate other hypotheses
        lean_hypotheses = " ".join(
            [
                f"(h{to_indices(i)} : {hyp.translate()})"
                for i, hyp in enumerate(hypotheses.get_non_identifiers())
            ]
        )

        # translate theses
        lean_theses = theses.translate()

        # full statement
        theorem_statement = f"theorem {self.lean_name} {lean_identifiers} {lean_hypotheses} : {lean_theses}"
        return f"{theorem_statement} := by\n"


class Example(Theorem):
    """Example class.
    Example consists of a theorem without name. Similar to the `example :` in lean.
    """

    # (()\s*((?:.|\s)+?))\s*(?:\n\s*\n\s*(?:.|\s)*|$)
    pattern: str = (
        # empty group to be able to reuse set_contents
        r"(()\s*"
        # Example statement (lazy matching to avoid matching the proof with it)
        r"((?:.|\s)+?))"
        # avoid extra blanks
        r"\s*"
        # group 2 possibilities : only example or example with proof
        r"(?:"
        # example with proof : proof must be separated by a blank line
        r"\n\s*\n\s*"
        # proof contents
        r"(?:.|\s)*"
        # if only example : end of string
        r"|$)"
    )

    def translate(self, **kwargs) -> str:
        hypotheses = self.statement.hypotheses
        theses = self.statement.theses
        # translate identifiers
        lean_identifiers = hypotheses.translate_identifiers()
        # translate other hypotheses
        lean_hypotheses = " ".join(
            [
                f"(h{to_indices(i)} : {hyp.translate()})"
                for i, hyp in enumerate(hypotheses.get_non_identifiers())
            ]
        )

        # translate theses
        lean_theses = theses.translate()

        # full statement
        theorem_statement = (
            f"example {lean_identifiers} {lean_hypotheses} : {lean_theses}"
        )
        return f"{theorem_statement} := by\n"
