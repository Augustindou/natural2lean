import Mathlib.Tactic.Ring
import LeanUtils.Parity

open Nat

theorem square_of_even_number_is_even (m : Nat) : (even m) → (even (m ^ 2)) := by
  intro H₁
  cases H₁ with 
  | intro n hn =>
    rw [hn]
    exact ⟨2 * n ^ 2, by ring⟩
