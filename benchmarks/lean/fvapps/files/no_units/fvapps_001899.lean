-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def possible_bipartition (n : Nat) (dislikes : List (List Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>