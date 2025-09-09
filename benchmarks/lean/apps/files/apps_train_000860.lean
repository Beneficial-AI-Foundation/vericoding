-- <vc-helpers>
-- </vc-helpers>

def countZerosInBinary (n : Nat) : Nat := sorry
def solveTestCase (n : Nat) : Nat := sorry

theorem zeros_count_nonneg (n : Nat) : 
  countZerosInBinary n ≥ 0 := sorry

theorem zeros_count_leq_len (n : Nat) : 
  ∃ binaryLen : Nat, countZerosInBinary n ≤ binaryLen := sorry

theorem solve_matches_count (n : Nat) :
  solveTestCase n = countZerosInBinary n := sorry

theorem power_two_zeros (i : Nat) (h : i > 0) :
  countZerosInBinary (2^i) = i := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_test_case 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_test_case 4

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_test_case 8

-- Apps difficulty: interview
-- Assurance level: guarded