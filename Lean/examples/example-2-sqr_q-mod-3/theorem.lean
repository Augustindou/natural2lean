import Mathlib.Tactic.Ring
import LeanUtils.Div

open Nat

theorem square_mod_3 (q : Nat) : (¬divisible 3 q) → (q^2 % 3 = 1) := by
  intros h₁
  repeat rw [divisible] -- not necessary here but useful for example 3
  have h_possibilities : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := mod_3_poss q

  -- divide cases into 3 goals
  cases h_possibilities with
  | inl h0 => 
    -- case 0
    contradiction
  | inr h1or2 => 
    cases h1or2 with
    | inl h1 => 
      -- case 1
      have q_rewrite : ∃k, q = 3 * k + 1 := mod_rewrite.mp h1
      have ⟨k, hk⟩ := q_rewrite
      have q_square : q^2 = 3 * (3 * k^2 + 2 * k) + 1  := by 
        calc
          q^2 = (3 * k + 1)^2 := by 
            try simp [*]
            try ring
          _ = 9 * k^2 + 6 * k + 1 := by ring
          _ = 3 * (3 * k^2 + 2 * k) + 1 := by ring
      exact mod_rewrite.mpr ⟨3 * k^2 + 2 * k, by assumption⟩
    | inr h2 => 
      -- case 2
      have q_rewrite : ∃k, q = 3 * k + 2 := mod_rewrite.mp h2
      have ⟨k, hk⟩ := q_rewrite
      have q_square : q^2 = 3 * (3 * k^2 + 4 * k + 1) + 1 := by 
        calc
          q^2 = (3 * k + 2)^2 := by 
            try simp [*]
            try ring
          _ = 3 * (3 * k^2 + 4 * k + 1) + 1 := by ring
      exact mod_rewrite.mpr ⟨3 * k^2 + 4 * k + 1, by assumption⟩