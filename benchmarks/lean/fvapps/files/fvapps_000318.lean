-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lengthOfLongestSubstring (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_bounds (s : String) :
  0 ≤ lengthOfLongestSubstring s ∧ lengthOfLongestSubstring s ≤ s.length := by
  sorry

theorem single_char_string (s : String) (h : s.data.eraseDups.length = 1) :
  lengthOfLongestSubstring s = 1 := by
  sorry

theorem empty_and_single (s : String) :
  (s = "") → lengthOfLongestSubstring s = 0 ∧
  (s.length = 1) → lengthOfLongestSubstring s = 1 := by
  sorry

theorem unique_chars (s : String) :
  s.data.eraseDups.length = s.length →
  lengthOfLongestSubstring s = s.length := by
  sorry

theorem concat_size (s₁ s₂ : String) :
  lengthOfLongestSubstring (s₁ ++ s₂) ≥ 
    max (lengthOfLongestSubstring s₁) (lengthOfLongestSubstring s₂) := by
  sorry
-- </vc-theorems>