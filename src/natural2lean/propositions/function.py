from ..utils.translatable import Translatable


class Function(Translatable):
    def __init__(self, name: str, args: list[Translatable]):
        self.name: str = name
        self.args: list[Translatable] = args

    def translate(
        self,
        hyp_name: str = None,
        proof: str = None,
        **kwargs,
    ) -> str:
        if bool(hyp_name) != bool(proof):
            raise ValueError(
                "Either both or neither of hyp_name and proof must be specified."
            )

        hyp_name = f"{hyp_name} : " if hyp_name else ""
        proof = f" := {proof}" if proof else ""

        return (
            hyp_name
            + self.name
            + " ("
            + ") (".join([arg.translate() for arg in self.args])
            + ")"
            + proof
        )
