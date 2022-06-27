from natural2lean import Translator
from natural2lean.lean_interaction.lean_feedback import raw_feedback
from pathlib import Path

translator = Translator()



print()

translator.new(r"Theorem Square mod 3: If $q$ is a natural not divisible by $3$, then $q^2 \mod 3 = 1$.")
print(translator.interpretation_feedback())
print()

translator.new(r"Considering the different possibilities of the modulo operation, we have $q \mod 3 \in \{ 0, 1, 2 \}$.")
print(translator.interpretation_feedback())
print()

translator.new(r"For the first case, as $q$ is not divisible by $3$, we have a contradiction.")
print(translator.interpretation_feedback())
print()

translator.new(r"For the second case, we have $q \mod 3 = 1$.")
print(translator.interpretation_feedback())
print()

translator.new(r"By definition of the modulo operation, we have $k \in \mathbb{N}$ such that $q = 3k + 1$.")
print(translator.interpretation_feedback())
print()

translator.new(r"By expansion, we have $q^2 = (3k+1)^2 = 9k^2+6k+1 = 3(3k^2 + 2k) + 1$.")
print(translator.interpretation_feedback())
print()

translator.new(r"Hence, $q^2 \mod 3 = 1$.")
print(translator.interpretation_feedback())
print()

translator.new(r"For the last case, by definition of the modulo operation, we have $k \in \mathbb{N}$ such that $q = 3k + 2$.")
print(translator.interpretation_feedback())
print()

translator.new(r"Following the same expansion, we have $q^2 = (3k+2)^2 = 3(3k^2+4k+1) +1$.")
print(translator.interpretation_feedback())
print()

translator.new(r"Hence, $q^2 \mod 3 = 1$ again.")
print(translator.interpretation_feedback())
print()

translator.new(r"Theorem square of q divisible by 3 means q is divisible by 3: If $q \in \mathbb{N}$ and $q^2$ is divisible by $3$, then $q$ is also divisible by $3$.")
print(translator.interpretation_feedback())
print()

translator.new(r"We will prove the contrapositive")
print(translator.interpretation_feedback())
print()

translator.new(r"By the 'square mod 3' theorem, we have $q^2 \mod 3 = 1$")
print(translator.interpretation_feedback())
print()

translator.new(r"Hence $q^2$ is not divisible by $3$.")
print(translator.interpretation_feedback())