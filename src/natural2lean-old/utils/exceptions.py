

class LeanError(Exception):
    """
    Exception when lean failed.
    """

class TranslationError(ValueError):
    """
    Exception when translation failed (system could not understand a statement).
    """
    