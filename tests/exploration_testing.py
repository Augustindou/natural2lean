from natural2lean import Translator
from natural2lean.lean_interaction.lean_feedback import raw_feedback
from pathlib import Path

translator = Translator()

print(raw_feedback("""import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"
open Nat

theorem square_of_q_divisible_by_3_means_q_is_divisible_by_3 (q : Nat) (h₀ : divisible (3) (q^2)) : divisible (3) (q) := by""", Path.home() / Path(".natural2lean")))


translator.new(r"Theorem square of q divisible by 3 means q is divisible by 3: If $q \in \mathbb{N}$ and $q^2$ is divisible by $3$, then $q$ is also divisible by $3$.")








