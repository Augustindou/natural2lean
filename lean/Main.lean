import LeanUtils
def main : IO Unit := IO.println s!"Hello, world!"
open Nat

example (a : Nat)  : b+1 > 2 := by
  have h₀ : 3 > 2 := by 
    calc
      3 > 2 := by try simp [*]; try ring
  dhes