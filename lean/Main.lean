import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"
open Nat

theorem square_mod_3 (q : Nat) (h0 : ¬ divisible (3) (q)) : q^2 % 3 = 1 := by
  have h1 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := mod_3_poss _

  rcases h1 with h1 | h1 | h1  contradiction  have h2 : q % 3 = 1 := by 
    calc
      q % 3 = 1 := by try simp [*]; try ring
  have ⟨k, h3⟩ : ∃ (k : Nat), q = 3*k + 1 := by 
    simp at *
    assumption
  have h4 : q^2 = 3*(3*k^2 + 2*k) + 1 := by 
    calc
      q^2 = (3*k+1)^2 := by try simp [*]; try ring
      _ = 9*k^2+6*k+1 := by try simp [*]; try ring
      _ = 3*(3*k^2 + 2*k) + 1 := by try simp [*]; try ring
  apply mod_rewrite.mpr; try exact ⟨_, by assumption⟩  have ⟨k, h2⟩ : ∃ (k : Nat), q = 3*k + 2 := by 
    simp at *
    assumption
  have h3 : q^2 = 3*(3*k^2+4*k+1) +1 := by 
    calc
      q^2 = (3*k+2)^2 := by try simp [*]; try ring
      _ = 3*(3*k^2+4*k+1) +1 := by try simp [*]; try ring
  apply mod_rewrite.mpr; try exact ⟨_, by assumption⟩