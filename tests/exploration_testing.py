from natural2lean import Translator
from natural2lean.lean_interaction.lean_feedback import raw_feedback
from pathlib import Path

translator = Translator()

translator.new(r"For any natural number $n$, $n^3 + 2n$ is divisible by $3$.")
translator.new(r"We will use induction on $n$.")
translator.new(r"The base case, $n = 0$, is trivial.")
translator.new(
    r"For $n = k+1$, the induction hypothesis gives us that $k^3 + 2k$ is divisible by $3$."
)
translator.new(r"Therefore, we have a natural number $z$ such that $k^3 + 2k = 3*z$.")
translator.new(
    r"By expansion, we can derive $(k+1)^3 + 2(k+1) = k^3 + 3k^2 + 5k + 3 = k^3 + 2k + 3(k^2 + k + 1) =3z + 3(k^2 + k + 1) = 3(z+k^2+k+1)$."
)
translator.new(r"Hence, $(k+1)^3 + 2(k+1)$ is divisible by $3$.")
