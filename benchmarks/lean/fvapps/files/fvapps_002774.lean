-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_diff (a b : List Int) : List Int := sorry

theorem array_diff_elements_from_a (a b : List Int) :
  ∀ x ∈ array_diff a b, x ∈ a := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_diff_no_elements_from_b (a b : List Int) :
  ∀ x ∈ array_diff a b, x ∉ b := sorry

theorem array_diff_preserves_order (a b : List Int) :
  array_diff a b = a.filter (fun x => x ∈ array_diff a b) := sorry

theorem array_diff_empty_b (a : List Int) :
  array_diff a [] = a := sorry

theorem array_diff_identical_lists (a : List Int) :
  array_diff a a = [] := sorry
-- </vc-theorems>