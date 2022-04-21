import Mathlib.Tactic.Ring
import LeanUtils.Parity
import LeanUtils.Div
import LeanUtils.Logic

open Nat

theorem square_mod_3 (q : Nat) : ¬ divisible (3) (q) → q^2 % 3 = 1 := by
      intros h0
      
