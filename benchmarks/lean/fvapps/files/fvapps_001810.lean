-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_range (lists : List (List Int)) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_contains_number_from_each_list (lists : List (List Int))
    (h1 : ∀ l ∈ lists, l.length > 0) :
  let result := find_smallest_range lists
  ∀ l ∈ lists, ∃ x ∈ l, result.1 ≤ x ∧ x ≤ result.2 := by
  sorry

theorem range_bounds (lists : List (List Int)) 
    (h1 : ∀ l ∈ lists, l.length > 0)
    (h2 : lists.length > 0) :
  let result := find_smallest_range lists
  (∃ l ∈ lists, ∃ x ∈ l, x = result.1) ∧
  (∃ l ∈ lists, ∃ x ∈ l, x = result.2) := by
  sorry
-- </vc-theorems>