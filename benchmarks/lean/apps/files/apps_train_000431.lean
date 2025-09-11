-- <vc-preamble>
def consecutive_numbers_sum (n : Nat) : Nat :=
  sorry

def isPrime (n : Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSquare (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_always_positive (n : Nat) (h : n > 0) : 
  consecutive_numbers_sum n ≥ 1 :=
  sorry

theorem result_less_than_input (n : Nat) (h : n > 0) :
  consecutive_numbers_sum n ≤ n :=
  sorry

theorem known_edge_cases :
  consecutive_numbers_sum 1 = 1 ∧ 
  consecutive_numbers_sum 2 = 1 ∧
  consecutive_numbers_sum 3 = 2 ∧
  consecutive_numbers_sum 4 = 1 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval consecutive_numbers_sum 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval consecutive_numbers_sum 9

/-
info: 4
-/
-- #guard_msgs in
-- #eval consecutive_numbers_sum 15
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible