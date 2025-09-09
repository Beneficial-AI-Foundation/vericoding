def maximum_swap (n : Nat) : Nat := sorry

def countDigit (d n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def numDigits (n : Nat) : Nat := sorry

theorem maximum_swap_result_ge (n : Nat) :
  maximum_swap n ≥ n := sorry

theorem maximum_swap_edge_cases :
  maximum_swap 0 = 0 ∧
  maximum_swap 1 = 1 ∧
  maximum_swap 10 = 10 ∧
  maximum_swap 99 = 99 := sorry

/-
info: 7236
-/
-- #guard_msgs in
-- #eval maximum_swap 2736

/-
info: 9973
-/
-- #guard_msgs in
-- #eval maximum_swap 9973

/-
info: 9913
-/
-- #guard_msgs in
-- #eval maximum_swap 1993

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible