-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_equal_subsequences (s: String) : String := sorry

theorem has_equal_subsequences_output_yes_or_no (s: String) :
  s ≠ "" → has_equal_subsequences s = "yes" ∨ has_equal_subsequences s = "no" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem has_equal_subsequences_duplicate_yes {s: String} {c: Char} :
  s.length ≥ 1 → has_equal_subsequences (String.mk [c, c] ++ s) = "yes" := sorry

theorem has_equal_subsequences_unique_no {s: String} :
  (∀ (i j : String.Pos), i.1 < s.length → j.1 < s.length → i ≠ j → s.get i ≠ s.get j) →
  has_equal_subsequences s = "no" := sorry

theorem has_equal_subsequences_empty_or_single_no (s: String) :
  s.length ≤ 1 → has_equal_subsequences s = "no" := sorry
-- </vc-theorems>