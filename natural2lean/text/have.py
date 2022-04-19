from ..structure.matching import Matching


class Have(Matching):
    """Have class.
    The 'have' keyword is used to identify expressions that we want to prove.
    """

    pattern: str = r"((.*)\s*have\s*(.*))"
