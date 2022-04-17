from ..structure.matching import Matching


class Identifier(Matching):
    """Just an identifier without operator"""

    pattern: str = r" *([a-zA-Z]\w*) *"

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return self.string.strip() == other.string.strip()
        return False

    def translate(self) -> str:
        return self.string.strip()
