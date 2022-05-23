import re
from .algebra import Algebra
from .translation_constants import SETS
from ..utils.unfolding import unfold
from ..utils.exceptions import MatchingError


class Identifier(Algebra):
    # starts with a letter and then anything alphanumeric, no spaces inside but allow spaces around
    pattern: str = r"\s*[a-zA-Z]\w*\s*"

    def __init__(self, string: str) -> None:
        # check for match
        if not re.fullmatch(self.pattern, string):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.string = string.strip()

    def translate(self, **kwargs) -> str:
        return self.string


class MultipleIdentifiers(Algebra):
    # start with an identifier possibly followed by a comma, then anything
    # this will allow for only one identifier
    pattern: str = f"({Identifier.pattern})" + r"(?:(,)(.*))?"

    def __init__(self, string: str) -> None:
        # check for match
        if not re.fullmatch(self.pattern, string):
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.string = string.strip()

        # get identifiers
        elements, separators = unfold(self.pattern, self.string)
        # an error will be raised here if there is a problem with an identifier
        self.identifiers: list[Identifier] = [Identifier(e) for e in elements]

    def translate(self, **kwargs) -> str:
        return " ".join([i.translate() for i in self.identifiers])


class IdentifiersInSet(MultipleIdentifiers):
    pattern: str = f"({MultipleIdentifiers.pattern})" + r"∈\s*(.+)"

    def __init__(self, string: str) -> None:
        # check for match
        match = re.fullmatch(self.pattern, string)
        if not match:
            raise MatchingError(
                f"Could not match {string} in {self.__class__.__name__}"
            )

        self.string = string.strip()

        self.identifiers = MultipleIdentifiers(match.group(1)).identifiers
        self.set = SETS[match.group(5).strip()]

    def translate(self, **kwargs) -> str:
        lean_identifiers = " ".join([i.translate() for i in self.identifiers])

        return f"({lean_identifiers} : {self.set.lean})"
