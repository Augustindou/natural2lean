class LeanError(Exception):
    """
    Exception when lean failed.
    """


class TranslationError(ValueError):
    """
    Exception when translation failed (system could not translate a statement).
    """


class ParsingError(ValueError):
    """
    Exception when parsing failed (system could not understand a statement).
    """


class MatchingError(ValueError):
    """
    Exception when matching failed (system could not match the string).
    """
