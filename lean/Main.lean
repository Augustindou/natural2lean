import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"
open Nat

theorem square_of_even_number_is_even (m : Nat) (h0 : even (m)) : even (m^2) := by
  have ⟨n, h1⟩ : ∃ (n : Nat), m = 2*n := by 
    simp at *
    assumption
  even (m^2)