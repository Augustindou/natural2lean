from .matching import Matching


class Proof(Matching):
    """Proof class.
    Proof matches anything. If the proof begins by the 'Proof' keyword, the keyword is not kept in the instance. This class should only be used when it is known that the contents of a string is a proof.

    Some examples of what Proof will match are :
        - Proof: by assumption
            -> will result in Proof("by assumption")
        - by assumption and the following development, ...
            -> will result in Proof("by assumption and the following development, ...")

    Some more information :
        - TODO
    """
    # (?:\s*[Pp]roof\s*?[.,:;!]*)?(?:\n\s*)?((?:.|\s)*)
    pattern = (
        # proof keyword (facultative), followed by any 'logical' punctuation (.,:;!) will be avoided
        r"(?:\s*[Pp]roof\s*?[.,:;!]*\s*?)?"
        # skip new lines
        r"(?:\n\s*)?"
        # content of the proof (until the end of the string)
        r"((?:.|\s)*)"
    )
