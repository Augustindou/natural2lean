import Mathlib.Init.Data.Nat.Basic

/- Div : functions and theorems relative to the division and modulo operations -/

namespace Nat
  def divisible (b a : Nat) : Prop := a % b = 0

  -- TODO : more general version working for any number
  theorem mod_3_poss (a : Nat) : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 :=
    -- copied from Mathlib.Init.Data.Nat.Lemmas (and modified from mod_two_eq_zero_or_one)
    match a % 3, @Nat.mod_lt a 3 (by simp) with
    | 0,   _ => Or.inl rfl
    | 1,   _ => Or.inr (Or.inl rfl)
    | 2,   _ => Or.inr (Or.inr rfl)
    | k+3, h => absurd h (λ h => not_lt_zero k (lt_of_succ_lt_succ (lt_of_succ_lt_succ (lt_of_succ_lt_succ h))))

  -- TODO : prove this... written as an axiom for now
  axiom mod_rewrite {a b m : Nat} : (a % b = m) ↔ ∃ k, a = b * k + m
end Nat

namespace Int
  def divisible (b a : Int) : Prop := a % b = 0
end Int

