-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_subsequences (s₁ s₂ : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_subsequences_non_negative (s₁ s₂ : String) :
  count_subsequences s₁ s₂ < 10^8 :=
  sorry

theorem count_subsequences_empty_needle (s : String) :
  count_subsequences "" s = 1 :=
  sorry

theorem count_subsequences_empty_haystack (s : String) :
  s ≠ "" → count_subsequences s "" = 0 :=
  sorry

theorem count_subsequences_identical (s : String) :
  s ≠ "" → count_subsequences s s = 1 :=
  sorry

theorem count_subsequences_repeated_chars (s : String) (n : Nat) :
  s ≠ "" →
  n > 0 → n ≤ 5 →
  let repeated := String.join (List.replicate n s)
  count_subsequences s repeated ≥ 1 :=
  sorry
-- </vc-theorems>