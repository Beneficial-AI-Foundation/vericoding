-- <vc-helpers>
-- </vc-helpers>

def last_substring (s : String) : String := sorry

theorem last_substring_returns_valid_suffix {s : String} (h : s.length > 0) :
  let result := last_substring s
  result.length > 0 ∧ s.endsWith result := sorry

theorem last_substring_is_lexicographically_largest {s : String} (h : s.length > 0) :
  let result := last_substring s
  ∀ (i : Nat), i < s.length → result ≥ s.drop i := sorry

theorem single_char_returns_itself {s : String} (h : s.length = 1) :
  last_substring s = s := sorry

theorem same_char_repeated_returns_whole_string {s : String} (h : s.length > 0)
  (h2 : ∀ (i j : String.Pos), s.get i = s.get j) :
  last_substring s = s := sorry

/-
info: 'bab'
-/
-- #guard_msgs in
-- #eval last_substring "abab"

/-
info: 'tcode'
-/
-- #guard_msgs in
-- #eval last_substring "leetcode"

/-
info: 'zzz'
-/
-- #guard_msgs in
-- #eval last_substring "zzz"

-- Apps difficulty: interview
-- Assurance level: unguarded