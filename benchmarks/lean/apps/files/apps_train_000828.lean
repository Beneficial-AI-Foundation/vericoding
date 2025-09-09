-- <vc-helpers>
-- </vc-helpers>

def find_largest_gcd_subarray (n : Nat) (arr : List Nat) : Nat :=
  sorry

theorem singleton_array {x : Nat} (h : x > 0) : 
  find_largest_gcd_subarray 1 [x] = 1 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_largest_gcd_subarray 4 [2, 4, 8, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_largest_gcd_subarray 5 [10, 10, 10, 5, 5]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_largest_gcd_subarray 3 [6, 12, 6]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible