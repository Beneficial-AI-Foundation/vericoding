-- <vc-preamble>
def List.isSubsetOf (l1 l2 : List α) [BEq α] : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def people_indexes (favorite_companies : List (List String)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem people_indexes_valid_indices
  (favorite_companies : List (List String)) :
  let result := people_indexes favorite_companies
  ∀ i ∈ result, i < favorite_companies.length :=
sorry

theorem people_indexes_empty :
  people_indexes [] = [] :=
sorry

/-
info: [0, 1, 4]
-/
-- #guard_msgs in
-- #eval people_indexes [["leetcode", "google", "facebook"], ["google", "microsoft"], ["google", "facebook"], ["google"], ["amazon"]]

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval people_indexes [["leetcode", "google", "facebook"], ["leetcode", "amazon"], ["facebook", "google"]]

/-
info: [0, 1, 2, 3]
-/
-- #guard_msgs in
-- #eval people_indexes [["leetcode"], ["google"], ["facebook"], ["amazon"]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible