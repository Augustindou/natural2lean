/- Parity : functions and theorems related to evenness and oddness of Naturals & Integers -/

namespace Nat
  def even (a : Nat) : Prop := ∃ (n : Nat), a = 2 * n
  def odd (a : Nat) : Prop := ¬ even a
end Nat

namespace Int
  def even (a : Int) : Prop := ∃ (n : Int), a = 2 * n
  def odd (a : Int) : Prop := ¬ even a
end Int
