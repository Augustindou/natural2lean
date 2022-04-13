from __future__ import annotations
import re


class Matching:

    pattern: str = None

    def __init__(self, string: str) -> None:
        """Initialises the instance.

        Args:
            string (str): content that was matched.
        """
        self.string = string
        self.__get_contents()

    @classmethod
    def match(cls, string: str) -> Matching:
        """Matches the string in argument to return the object (calls the constructor with the first group found)

        Args:
            string (str): string to match.

        Returns:
            Matching: an object of the right type, containing the matched string and its possible contents. Returns None if no match.
        """
        m = re.fullmatch(cls.pattern, string)
        if m == None:
            return None
        return cls.__init__(m.group(1))

    def __get_contents(self) -> None:
        """Matches recursively to extract the contents and adds it to self.contents. The __get_contents method is only called from the constructor and should have access to self.string."""
        self.contents = []
        raise NotImplementedError

    def translate(self) -> str:
        """Translates the instance and its contents into the lean4 equivalent.

        Returns:
            str: the lean4 equivalent of the instance.
        """
        raise NotImplementedError
