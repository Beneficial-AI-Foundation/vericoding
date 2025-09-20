-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestPalindrome (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longestPalindrome_nonnegative (s : String) :
  longestPalindrome s ≥ 0 := sorry

theorem longestPalindrome_leq_alphanum_count (s : String) :
  longestPalindrome s ≤ (s.toList.filter Char.isAlphanum).length := sorry

theorem longestPalindrome_single_char (s : String) (h1 : s.length = 1) 
  (h2 : Char.isAlphanum (s.get 0)) :
  longestPalindrome s = 1 := sorry

theorem longestPalindrome_parity_odd (s : String) :
  let chars := s.toLower.toList.filter Char.isAlphanum
  let counts := fun c => (chars.filter (· = c)).length
  (∃ c, counts c % 2 = 1) →
  longestPalindrome s % 2 = 1 := sorry

theorem longestPalindrome_parity_even (s : String) :
  let chars := s.toLower.toList.filter Char.isAlphanum
  let counts := fun c => (chars.filter (· = c)).length
  (¬∃ c, counts c % 2 = 1) →
  longestPalindrome s > 0 →
  longestPalindrome s % 2 = 0 := sorry
-- </vc-theorems>