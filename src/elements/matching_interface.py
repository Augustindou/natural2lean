from __future__ import annotations


class MatchingBaseClass:
    """Interface for a class capable of matching a sentence.
    @attribute __pattern: str, a regex for matching the specific concept"""

    __pattern: str = None

    def __init__(self, string: str) -> None:
        raise NotImplementedError

    @classmethod
    def match(self, string: str) -> MatchingBaseClass:
        raise NotImplementedError
