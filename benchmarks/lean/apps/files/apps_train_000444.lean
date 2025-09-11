-- <vc-preamble>
def maximum_swap (n : Nat) : Nat := sorry

def countDigit (d n : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numDigits (n : Nat) : Nat := sorry

theorem maximum_swap_result_ge (n : Nat) :
  maximum_swap n ≥ n := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible