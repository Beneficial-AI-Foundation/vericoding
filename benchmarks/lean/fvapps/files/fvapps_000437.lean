-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_duplicate_letters (s : String) : String := sorry

theorem output_is_subset_of_input (s : String) (h : s.length > 0) :
  ∀ (c : Char), c ∈ (remove_duplicate_letters s).data → c ∈ s.data := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_has_no_duplicates (s : String) (h : s.length > 0) :
  ∀ c, (remove_duplicate_letters s).data.count c ≤ 1 := sorry
-- </vc-theorems>