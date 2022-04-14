from ..structure import Matching


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
