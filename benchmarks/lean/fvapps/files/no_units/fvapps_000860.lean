-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countZerosInBinary (n : Nat) : Nat := sorry
def solveTestCase (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_count_nonneg (n : Nat) : 
  countZerosInBinary n ≥ 0 := sorry

theorem zeros_count_leq_len (n : Nat) : 
  ∃ binaryLen : Nat, countZerosInBinary n ≤ binaryLen := sorry

theorem solve_matches_count (n : Nat) :
  solveTestCase n = countZerosInBinary n := sorry

theorem power_two_zeros (i : Nat) (h : i > 0) :
  countZerosInBinary (2^i) = i := sorry
-- </vc-theorems>