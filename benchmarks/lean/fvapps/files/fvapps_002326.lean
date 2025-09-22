-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitString (s: String) : List String :=
  sorry

def lengthOfLastWord (s: String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_of_last_word_nonnegative (s: String) :
  lengthOfLastWord s ≥ 0 :=
sorry

theorem length_of_last_word_matches_split (s: String) :
  lengthOfLastWord s > 0 →
  match splitString s with
  | [] => True
  | xs => lengthOfLastWord s = xs.getLast!.length
  :=
sorry

theorem length_of_last_word_empty_for_blank (s: String) :
  s.trim.isEmpty → lengthOfLastWord s = 0 :=
sorry

theorem length_of_last_word_ignores_trailing_spaces (s: String) :
  lengthOfLastWord s = lengthOfLastWord s.trim :=
sorry
-- </vc-theorems>