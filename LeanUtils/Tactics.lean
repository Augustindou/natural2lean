namespace BetterSimp

  attribute [simp] 
    -- addition
      -- zero & one
      Nat.add_zero
      Nat.zero_add
      -- succ
      Nat.add_succ
      Nat.succ_add
      -- swapping
      Nat.add_assoc
      Nat.add_comm
      Nat.add_left_comm
    
    -- multiplication
      -- zero & one
      Nat.mul_zero
      Nat.zero_mul
      Nat.mul_one
      Nat.one_mul
      -- succ
      Nat.mul_succ
      Nat.succ_mul
      -- swapping 
      Nat.mul_comm
      Nat.mul_assoc
      Nat.mul_left_comm
    -- powers
      -- zero & one
      Nat.pow_zero
      -- succ
      Nat.pow_succ
    -- multiplication to addition
    Nat.left_distrib
    Nat.right_distrib

end BetterSimp