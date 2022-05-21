from natural2lean import Translator

translator = Translator()

translator.new_theorem(
    "Theorem Square of even number is even: if $m \in \mathbb{N}$ is even, then $m^2$ is even."
)

translator.new_statement(
    "By definition, if $m$ is even, we have a natural number $n$ such that $m = 2n$."
)

translator.new_statement("Therefore we have $m^2 = (2n)^2 = 4n^2 = 2(2n^2)$.")

translator.new_statement("Therefore $m^2$ is even.")
