import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"
open Nat

theorem square_of_even_number_is_even (m : Nat) (h₀ : even (m)) : even (m^2) := by
  have ⟨n, h₁⟩ : ∃ (n : Nat), m = 2*n := by 
    simp at *
    assumption
  have h₂ : m^2 = 2*(2*n^2) := by 
    calc
      m^2 = (2*n)^2 := by try simp [*]; try ring
      _ = 4*n^2 := by try simp [*]; try ring
      _ = 2*(2*n^2) := by try simp [*]; try ring
  try exact ⟨_, by assumption⟩