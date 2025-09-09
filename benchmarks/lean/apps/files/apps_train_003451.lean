-- <vc-helpers>
-- </vc-helpers>

def gematria (s : String) : Nat :=
  sorry

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

/-
info: 775
-/
-- #guard_msgs in
-- #eval gematria "love"

/-
info: 716
-/
-- #guard_msgs in
-- #eval gematria "JAELS"

/-
info: 738
-/
-- #guard_msgs in
-- #eval gematria "Devil"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible