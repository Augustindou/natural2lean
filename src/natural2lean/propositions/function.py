from ..utils.translatable import Translatable


class Function(Translatable):
    def __init__(self, name: str, args: list[Translatable]):
        self.name: str = name
        self.args: list[Translatable] = args

    def translate(self, **kwargs) -> str:
        return (
            self.name + " (" + ") (".join([arg.translate() for arg in self.args]) + ")"
        )
