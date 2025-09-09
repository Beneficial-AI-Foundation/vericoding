-- <vc-helpers>
-- </vc-helpers>

def possible_bipartition (n : Nat) (dislikes : List (List Nat)) : Bool :=
  sorry

theorem empty_dislikes_always_possible {n : Nat} {dislikes : List (List Nat)} :
  n ≥ 2 → dislikes = [] → possible_bipartition n dislikes = true := by
  sorry

theorem single_pair_always_possible {n : Nat} {dislikes : List (List Nat)} :
  n ≥ 2 → dislikes.length = 1 → possible_bipartition n dislikes = true := by
  sorry

theorem triangle_impossible :
  possible_bipartition 3 [[1,2], [2,3], [1,3]] = false := by
  sorry

theorem simple_chain_possible :
  possible_bipartition 4 [[1,2], [2,3], [3,4]] = true := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval possible_bipartition 4 [[1, 2], [1, 3], [2, 4]]

/-
info: False
-/
-- #guard_msgs in
-- #eval possible_bipartition 3 [[1, 2], [1, 3], [2, 3]]

/-
info: False
-/
-- #guard_msgs in
-- #eval possible_bipartition 5 [[1, 2], [2, 3], [3, 4], [4, 5], [1, 5]]

-- Apps difficulty: interview
-- Assurance level: unguarded