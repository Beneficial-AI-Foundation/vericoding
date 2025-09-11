-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_obtain_permutation (n m : Nat) (perm : List Nat) (pairs : List (List Nat)) : String := sorry

theorem permutation_result_is_valid (n m : Nat) (perm : List Nat) (pairs : List (List Nat)) :
  n > 0 → m > 0 → perm.Nodup → pairs ≠ [] →
  let result := can_obtain_permutation n m perm pairs
  (result = "Possible" ∨ result = "Impossible") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorted_permutation_possible (n m : Nat) (perm : List Nat) (pairs : List (List Nat)) :
  n > 0 → m > 0 → perm.Nodup → pairs ≠ [] →
  (∀ i j, i < j → i < perm.length → j < perm.length → perm[i]! ≤ perm[j]!) →
  can_obtain_permutation n m perm pairs = "Possible" := sorry

theorem result_invariant_under_pair_reordering (n m : Nat) (perm : List Nat) (pairs : List (List Nat)) :
  n > 0 → m > 0 → perm.Nodup → pairs ≠ [] →
  can_obtain_permutation n m perm pairs = can_obtain_permutation n m perm pairs.reverse := sorry

theorem single_pair_covering_whole_array (n : Nat) (perm : List Nat) :
  n > 0 → perm.Nodup →
  can_obtain_permutation n 1 perm [[1,n]] = "Possible" := sorry

theorem non_overlapping_single_element_pairs (n : Nat) (perm : List Nat) :
  n > 0 → perm.Nodup →
  let pairs := List.range n |> List.map (fun i => [i+1,i+1])
  (∀ i j, i < j → i < perm.length → j < perm.length → perm[i]! ≤ perm[j]!) →
  can_obtain_permutation n n perm pairs = "Possible" := sorry

theorem non_overlapping_single_element_pairs_unsorted (n : Nat) (perm : List Nat) :
  n > 0 → perm.Nodup →
  let pairs := List.range n |> List.map (fun i => [i+1,i+1])
  (∃ i j, i < j ∧ i < perm.length ∧ j < perm.length ∧ perm[i]! > perm[j]!) →
  can_obtain_permutation n n perm pairs = "Impossible" := sorry

/-
info: 'Possible'
-/
-- #guard_msgs in
-- #eval can_obtain_permutation 7 4 [3, 1, 2, 4, 5, 7, 6] [[1, 2], [4, 4], [6, 7], [2, 3]]

/-
info: 'Impossible'
-/
-- #guard_msgs in
-- #eval can_obtain_permutation 4 2 [2, 1, 3, 4] [[2, 4], [2, 3]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded