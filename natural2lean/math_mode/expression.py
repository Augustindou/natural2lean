from ..structure import Matching


class Expression(Matching):
    pattern = (
        # opening group
        r"("
        # <anything> <letter/number> <operator> <letter/number> <anything> : a * b, 4 + a, ...
        r"(?:.*\w+(?:\)| )*[+\-*/^%](?:\(| )*\w+.*)"
        # <minus> <letter/number> <anything> : -2*a, -2, -3+a
        r"|(?:(?:\(| )*\-\w(?:\(| )*.*)"
        # closing group
        r")"
    )

    def __get_contents(self) -> None:
        self.contents = []
        raise NotImplementedError

    def translate(self) -> str:
        raise NotImplementedError
