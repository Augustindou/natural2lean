import LeanUtils.Div
import LeanUtils.Logic
import LeanUtils.Specific

open Nat

theorem square_of_q_divisible_by_3_means_q_is_divisible_by_3 (q : Nat) : divisible 3 (q^2) → divisible 3 q := by 
  have contrap : ¬(divisible 3 q) → ¬(divisible 3 (q^2)) := by 
    repeat rw [divisible]
    intros h₁
    have h₂ : q^2 % 3 = 1 := by
      apply square_mod_3 q h₁

    simp [*]

  exact contrapositive.mpr contrap