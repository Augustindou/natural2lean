from ..structure import Matching


class Equation(Matching):
    __pattern = r"((?:.*\w+(?:\)| )*[=≤≥<>](?:\(| )*\w+.*))" # TODO

    def __get_contents(self) -> None:
        self.contents = []
        raise NotImplementedError

    def translate(self) -> str:
        raise NotImplementedError
