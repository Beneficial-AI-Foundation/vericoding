-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_vowels (s : String) (k : Nat) : Nat :=
sorry

def count_vowels (s : String) : Nat :=
sorry

def is_vowel (c : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_vowels_monotonic {s : String} {k : Nat}
  (h1 : k < String.length s) :
  max_vowels s k ≤ max_vowels s (k + 1) :=
sorry

theorem max_vowels_empty {k : Nat}
  (h1 : k > 0) :
  max_vowels "" k = 0 :=
sorry
-- </vc-theorems>