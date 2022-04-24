import LeanUtils.Tactic
open Nat

example (m : Nat) (h0 : even (m)) : even (m^2) := by
  have ⟨n, h1⟩ : ∃ (n : Nat), m = 2*n := by 
    simp at *
    assumption
  have h2 : m^2 = 2*(2*n^2) := by 
    calc
      m^2 = (2*n)^2 := by try simp [*]; try ring
      _ = 4*n^2 := by try simp [*]; try ring
      _ = 2*(2*n^2) := by try simp [*]; try ring