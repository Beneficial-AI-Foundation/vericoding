def find_largest_subset_with_mex (n m : Nat) (arr : List Nat) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def mex (arr : List Nat) : Nat :=
  sorry

theorem find_largest_subset_result_valid (n m : Nat) (arr : List Nat) :
  let result := find_largest_subset_with_mex n m arr
  result ≤ n := sorry

theorem find_largest_subset_result_cases (n m : Nat) (arr : List Nat) :
  let result := find_largest_subset_with_mex n m arr
  (result = -1 ∨ result = n ∨ result = n - (List.count m arr)) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_largest_subset_with_mex 3 3 [1, 2, 4]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_largest_subset_with_mex 4 2 [1, 3, 4, 5]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_largest_subset_with_mex 3 5 [1, 2, 3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible