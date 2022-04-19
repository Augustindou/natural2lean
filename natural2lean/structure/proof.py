import re
from .matching import Unmatchable


class Proof(Unmatchable):
    """Proof class.
    If the proof begins by the 'Proof' keyword, the keyword is not kept in the instance.

    Some more information :
        - TODO
    """

    # (?:\s*[Pp]roof\s*?[.,:;!]*)?\s*((?:.|\s)+)
    pattern: str = (
        # proof keyword (facultative), followed by any 'logical' punctuation (.,:;!) will be avoided
        r"(?:\s*[Pp]roof\s*?[.,:;!]*\s*?)?"
        # skip blanks
        r"\s*"
        # content of the proof (until the end of the string)
        r"((?:.|\s)+)"
    )

    def set_contents(self):
        # skip the proof keyword
        self.string = re.fullmatch(self.pattern, self.string).group(1)
        # TODO
