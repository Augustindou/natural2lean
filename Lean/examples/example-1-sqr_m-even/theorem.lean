import LeanUtils.Tactic

open Nat

theorem square_of_even_number_is_even (m : Nat) : (even m) → (even (m ^ 2)) := by
  intros h₁
  obtain ⟨n, h₂⟩ : ∃ (n : Nat), m = 2 * n :=
    by simp at *; assumption
  have h₃ : m^2 = 2*(2*n^2) := by 
    calc
      m^2 = (2*n)^2 := by 
        try simp [*]
        try ring
      _ = 4*n^2 := by 
        ring
      _ = 2*(2*n^2) := by 
        ring

  exact ⟨_, by assumption⟩

