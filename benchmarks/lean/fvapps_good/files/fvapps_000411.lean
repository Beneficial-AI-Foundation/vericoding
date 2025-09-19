-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def last_substring (s : String) : String := sorry

theorem last_substring_returns_valid_suffix {s : String} (h : s.length > 0) :
  let result := last_substring s
  result.length > 0 ∧ s.endsWith result := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem last_substring_is_lexicographically_largest {s : String} (h : s.length > 0) :
  let result := last_substring s
  ∀ (i : Nat), i < s.length → result ≥ s.drop i := sorry

theorem single_char_returns_itself {s : String} (h : s.length = 1) :
  last_substring s = s := sorry

theorem same_char_repeated_returns_whole_string {s : String} (h : s.length > 0)
  (h2 : ∀ (i j : String.Pos), s.get i = s.get j) :
  last_substring s = s := sorry
-- </vc-theorems>