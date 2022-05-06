import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"

open Nat

theorem square_mod_3 (q : Nat) : (¬divisible 3 q) → (q^2 % 3 = 1) := by
  intros h₁
  apply mod_rewrite.mpr
  have h2 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := mod_3_poss _

  -- divide cases into 3 goals
  rcases h2 with h2 | h2 | h2

  contradiction

  have ⟨k, h3⟩ : ∃ (k : Nat), q = 3 * k + 1 := by 
    simp at *
    assumption