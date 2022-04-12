import Mathlib.Tactic.Ring
import LeanUtils.Parity

open Nat

theorem square_of_even_number_is_even (m : Nat) : (even m) → (even (m ^ 2)) := by
  intro h₁
  have ⟨n, h₂⟩ := h₁
  have h₃ : m^2 = 2*(2*n^2) := by 
    calc
      m^2 = (2*n)^2 := by rw [h₂]
      _ = 4*n^2 := by ring
      _ = 2*(2*n^2) := by ring
    
  exact ⟨2 * n ^ 2, h₃⟩
