-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findJane (n : Nat) : Nat := sorry 

theorem findJane_non_negative (n : Nat) 
  (h : n ≥ 2) : 
  findJane n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem findJane_less_than_n (n : Nat)
  (h : n ≥ 2) :
  findJane n < n := sorry

theorem findJane_formula (n : Nat)
  (h : n ≥ 2) :
  findJane n = (n-1)/2 := sorry

theorem findJane_small_cases :
  findJane 2 = 0 ∧ 
  findJane 3 = 1 ∧
  findJane 4 = 1 ∧
  findJane 5 = 2 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_jane 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_jane 10

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_jane 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded