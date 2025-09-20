-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def classify_feedback (s : String) : String := sorry

def containsSubstring (s : String) (sub : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem classify_feedback_returns_valid_output (s : String) (h : s.length > 0) :
  (classify_feedback s = "Good" ∨ classify_feedback s = "Bad") := sorry

theorem good_feedback_contains_pattern (s : String) (h : s.length > 0) :
  classify_feedback s = "Good" → (containsSubstring s "010" ∨ containsSubstring s "101") := sorry

theorem no_pattern_implies_bad (s : String) (h : s.length > 0) :
  ¬(containsSubstring s "010" ∨ containsSubstring s "101") → classify_feedback s = "Bad" := sorry

theorem size_three_good_iff_pattern (s : String) (h : s.length = 3) :
  classify_feedback s = "Good" ↔ (s = "010" ∨ s = "101") := sorry

theorem short_string_is_bad (s : String) (h : s.length < 3) :
  classify_feedback s = "Bad" := sorry
-- </vc-theorems>