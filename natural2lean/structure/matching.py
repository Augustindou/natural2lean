from __future__ import annotations
import re


class Matching:
    """Matching class.
    This is the base class for all the classes that are used in the matching process.

    Some information :
        - The `pattern` allows the classmethod `match` to extract information. The `match` method will call the constructor with the first regex group in the `pattern`.
        - The `translate` method returns the `lean4` equivalent of the expression.
    """

    pattern: str = None

    def __init__(self, string: str) -> None:
        """Initialises the instance.

        Args:
            string (str): content that was matched.
        """
        self.string = string
        self.set_contents()
        self.detect_errors()

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
        return cls(m.group(1))

    def set_contents(self):
        """Extract the contents of a concept. The `set_contents` method should only be called from the constructor and should have access to `self.string`."""
        pass

    def detect_errors(self):
        """Detects errors in the instance. The `detect_errors` method should only be called after `set_contents`."""
        pass

    def translate(self) -> str:
        """Translates the instance and its contents into the lean4 equivalent.

        Returns:
            str: the lean4 equivalent of the instance.
        """
        raise NotImplementedError
