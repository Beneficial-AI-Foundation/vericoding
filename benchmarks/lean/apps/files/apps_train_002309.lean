-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def majorityElement (xs : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_majority {x : Int} :
  majorityElement [x] = x :=
  sorry

theorem repeated_element_majority (lst : List Int) (x : Int) :
  majorityElement (List.replicate (lst.length + 1) x) = x :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval majority_element [3, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval majority_element [2, 2, 1, 1, 1, 2, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval majority_element [1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded