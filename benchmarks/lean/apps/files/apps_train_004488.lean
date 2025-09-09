-- <vc-helpers>
-- </vc-helpers>

def duplicates (arr : List Int) : Nat :=
  sorry

theorem duplicates_non_negative (arr : List Int) :
  duplicates arr ≥ 0 := by
  sorry

theorem duplicates_bound (arr : List Int) :  
  duplicates arr ≤ arr.length / 2 := by
  sorry

theorem duplicates_empty :
  duplicates [] = 0 := by
  sorry

theorem duplicates_singleton (x : Int) :
  duplicates [x] = 0 := by
  sorry

theorem duplicates_all_equal (x : Int) (n : Nat) :
  duplicates (List.replicate (4 * n) x) = 2 * n := by
  sorry

theorem duplicates_concatenation (arr1 arr2 : List Int) :
  duplicates (arr1 ++ arr2) ≥ duplicates arr1 + duplicates arr2 := by
  sorry

theorem duplicates_perm (arr1 arr2 : List Int) :
  List.Perm arr1 arr2 → duplicates arr1 = duplicates arr2 := by
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval duplicates [1, 2, 2, 20, 6, 20, 2, 6, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval duplicates [1000, 1000]

/-
info: 0
-/
-- #guard_msgs in
-- #eval duplicates []

-- Apps difficulty: introductory
-- Assurance level: guarded