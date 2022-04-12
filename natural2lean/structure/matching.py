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
        """Matches the string in argument to return the object 

        Args:
            string (str): _description_

        Returns:
            Matching: _description_
        """
        m = re.fullmatch(cls.__pattern, string)
        if m == None:
            return None
        return cls.__init__(m.group(1))
    
    def translate(self) -> str:
        raise NotImplementedError
