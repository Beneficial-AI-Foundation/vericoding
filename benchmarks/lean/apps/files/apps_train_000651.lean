-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_minimum_array_sum (arr : List Nat) : Nat := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_minimum_sum {x : Nat} (h : x > 0) : 
  find_minimum_array_sum [x] = x := sorry

theorem same_number {n : Nat} {x : Nat} (h : n ≥ 2) (h₁ : x > 0) :
  find_minimum_array_sum (List.replicate n x) = n * x := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_minimum_array_sum [1]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_minimum_array_sum [2, 4, 6]

/-
info: 12
-/
-- #guard_msgs in
-- #eval find_minimum_array_sum [3, 6, 9, 12]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible