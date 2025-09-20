-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_anagram_pairs (s : String) : Nat :=
  sorry

def reverseString (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_anagram_pairs_nonneg (s : String) :
  find_anagram_pairs s ≥ 0 :=
sorry

theorem find_anagram_pairs_empty_or_single (s : String) :
  s.length ≤ 1 → find_anagram_pairs s = 0 :=
sorry
-- </vc-theorems>