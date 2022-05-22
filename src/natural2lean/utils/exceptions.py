class LeanError(Exception):
    """
    Exception when lean failed.
    """


class NoConclusion(ValueError):
    """
    Exception when a conclusion to a goal could not be found.
    """


class TranslationError(ValueError):
    """
    Exception when translation failed (system could not translate a statement).
    """


class MatchingError(ValueError):
    """
    Exception when matching failed (system could not match the string).
    """
