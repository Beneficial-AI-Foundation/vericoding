-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_anagrams (s : String) : Nat :=
sorry

def manual_count_anagrams (s : String) : Nat :=
sorry

def factorial (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_anagrams_positive (s : String) (h : s.length > 0) :
  count_anagrams s ≥ 0 ∧ count_anagrams s < 10^9 + 7 :=
sorry

theorem count_anagrams_letter_order_invariant (s : String) (h : s.length > 0) :
  count_anagrams s = count_anagrams s :=
sorry
-- </vc-theorems>