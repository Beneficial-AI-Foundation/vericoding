-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_cobra_temple (heights : List Nat) : Bool := sorry

theorem valid_cobra_sequences {peak : Nat} (h : peak > 0) (h2 : peak ≤ 10) :
  let ascending := List.range' 1 peak
  let descending := List.reverse (List.range' 1 (peak - 1))
  check_cobra_temple (ascending ++ descending) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem even_length_rejected {heights : List Nat} (h : heights.length % 2 = 0) 
  (h2 : heights.length ≥ 3) (h3 : ∀ x ∈ heights, x ≥ 1 ∧ x ≤ 100) :
  check_cobra_temple heights = false := sorry

theorem non_one_endpoints_rejected {heights : List Nat} 
  (h : heights.length % 2 = 1)
  (h2 : heights.length ≥ 3) 
  (h3 : ∀ x ∈ heights, x ≥ 2 ∧ x ≤ 100) :
  check_cobra_temple heights = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_cobra_temple [1, 2, 3, 2, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval check_cobra_temple [2, 3, 4, 5, 4, 3, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval check_cobra_temple [1, 2, 3, 4, 3, 2, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded