-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_segments (s : String) : Nat := sorry

theorem count_segments_empty :
  count_segments "" = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_segments_basic_cases :
  count_segments "Hello world" = 2 ∧
  count_segments "   spaces   around   " = 2 := sorry
-- </vc-theorems>