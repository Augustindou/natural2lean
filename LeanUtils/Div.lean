/- Div : functions and theorems relative to the division and modulo operations -/

namespace Nat
  def divisible (b a : Nat) : Prop := a % b = 0

  -- TODO : prove these... written as an axiom for now
  axiom mod_rewrite {a b m : Nat} : (a % b = m) ↔ ∃ k, a = b * k + m
  axiom mod_3_poss (a : Nat) : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2
end Nat

namespace Int
  def divisible (b a : Int) : Prop := a % b = 0
end Int

