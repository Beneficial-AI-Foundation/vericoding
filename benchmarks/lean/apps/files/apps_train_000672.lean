-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_star_value (arr : Array Nat) : Nat := sorry

def countDivisible (arr : Array Nat) (i : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_star_value (x : Nat) (h : x > 0) : 
  find_max_star_value #[x] = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_star_value #[8, 1, 28, 4, 2, 6, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_max_star_value #[1, 2, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_max_star_value #[3, 6, 9]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible