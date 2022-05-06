
from natural2lean.structure.matching import Translatable


def interactive_mode():
    pass

def get_statement() -> Translatable:
    pass

def match_statement(input: str):
    # match statement
    for possibility in STATEMENT_POSSIBILITIES:
        try:
            match = possibility.match(input)
        except ValueError:
            match = None
        if match is not None:
            return match
    return None