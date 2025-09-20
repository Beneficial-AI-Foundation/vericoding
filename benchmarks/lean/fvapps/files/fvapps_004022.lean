-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def palindrome : (n : Int) → String ⊕ Bool :=
sorry

def countOddDigits (n : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem negative_numbers {n : Int} (h : n < 0) : palindrome n = Sum.inl "Not valid" :=
sorry

theorem different_digits_odd_count {n : Int} (h1 : n ≥ 100) (h2 : n ≤ 9999)
  (h3 : countOddDigits n > 1) : palindrome n = Sum.inr false :=
sorry

theorem non_integers_text (s : String) : palindrome 0 = Sum.inl "Not valid" :=
sorry

theorem non_integers_dec (d : Float) : palindrome 0 = Sum.inl "Not valid" :=
sorry

theorem single_digits {n : Int} (h1 : n ≥ 0) (h2 : n ≤ 9) :
  palindrome n = Sum.inr false :=
sorry

theorem repeated_digits {n : Int} (h1 : n ≥ 1) (h2 : n ≤ 9) :
  palindrome (n * 11) = Sum.inr true :=
sorry
-- </vc-theorems>