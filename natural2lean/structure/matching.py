from __future__ import annotations
import re

class Matching:

    __pattern: str = None

    def __init__(self, string: str) -> None:
        self.string = string
        self.contents = []
        raise NotImplementedError

    @classmethod
    def match(cls, string: str) -> Matching:
        """Matches the string in argument to return the object (calls the constructor with the first group found)

        Args:
            string (str): string to match.

        Returns:
            Matching: an object of the right type, containing the matched string and its possible contents. Returns None if no match.
        """
        m = re.fullmatch(cls.__pattern, string)
        if m == None:
            return None
        return cls.__init__(m.group(1))
    
    def translate(self) -> str:
        """Translates the instance and its contents into the lean4 equivalent.

        Returns:
            str: the lean4 equivalent of the instance.
        """
        raise NotImplementedError
