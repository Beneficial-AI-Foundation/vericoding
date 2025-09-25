-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def duplicates (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>