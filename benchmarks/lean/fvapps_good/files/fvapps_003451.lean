-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gematria (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gematria_returns_nat (s : String) :
  gematria s ≥ 0 :=
  sorry

theorem gematria_case_insensitive (s : String) :
  gematria s = gematria s.toLower ∧
  gematria s = gematria s.toUpper :=
  sorry

theorem gematria_concatenation (s₁ s₂ : String) :
  gematria (s₁ ++ s₂) = gematria s₁ + gematria s₂ :=
  sorry
-- </vc-theorems>