from .matching import Matching


class Proof(Matching):
    # (?:\s*[Pp]roof.*){0,1}\n\s*((?:.|\s)*)
    pattern = (
        # proof keyword (facultative), followed by anything (considered not important)
        r"((?:\s*[Pp]roof.*){0,1}"
        # at least one new line
        r"\n\s*"
        # content of the proof (until the end of the string)
        r"(?:.|\s)*)"
    )
