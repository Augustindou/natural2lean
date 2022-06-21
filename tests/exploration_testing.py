from natural2lean import Translator
from natural2lean.lean_interaction.lean_feedback import raw_feedback
from pathlib import Path

translator = Translator()


translator.new(r"Theorem Square of even number is even: if $m \in \mathbb{N}$ is even, then $m^2$ is even.")
translator.new(r"By definition, if $m$ is even, we have a natural number $n$ such that $m = 2n$.")
translator.new(r"Therefore we have $m^2 = (2n)^2 = 4n^2 = 2(2n^2)$")
translator.new(r"Hence, $m^2$ is even.")




