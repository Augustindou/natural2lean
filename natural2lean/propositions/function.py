from __future__ import annotations

from ..structure.matching import Translatable


class Function(Translatable):
    # TODO description

    def __init__(
        self, function_name: str, args: list[Translatable], original_string: str
    ):
        self.function_name: str = function_name
        self.args: list[Translatable] = args
        self.original_string: str = original_string

    def translate(self) -> str:
        return (
            f"{self.function_name} ("
            + ") (".join([arg.translate() for arg in self.args])
            + ")"
        )
