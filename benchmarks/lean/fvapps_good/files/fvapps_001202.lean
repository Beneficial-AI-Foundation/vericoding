-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern_gen (k : Nat) : Array String := sorry

theorem pattern_gen_row_count {k : Nat} (h : k > 0) :
  (pattern_gen k).size = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_gen_first_element {k : Nat} (h : k > 0) :
  ((pattern_gen k).get! 0).data.get! 0 = '1' := sorry

theorem pattern_gen_all_digits {k : Nat} (h : k > 0) :
  ∀ i < (pattern_gen k).size,
  ∀ j < ((pattern_gen k).get! i).data.length,
  let c := ((pattern_gen k).get! i).data.get! j;
  c.isDigit := sorry
-- </vc-theorems>