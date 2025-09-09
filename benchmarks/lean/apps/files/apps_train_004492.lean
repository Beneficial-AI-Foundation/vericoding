-- <vc-helpers>
-- </vc-helpers>

def fisHex (s : String) : Nat :=
  sorry

theorem fisHex_empty :
  fisHex "" = 0 :=
sorry

theorem fisHex_valid_chars_only {s : String} :
  let validChars := s.data.filter (fun c => c ∈ ['a', 'b', 'c', 'd', 'e', 'f', 'A', 'B', 'C', 'D', 'E', 'F'])
  fisHex s = fisHex (String.mk validChars) :=
sorry

theorem fisHex_concat {s₁ s₂ : String} :
  fisHex (s₁ ++ s₂) = fisHex s₁ ^^^ fisHex s₂ :=
sorry

theorem fisHex_case_insensitive {s : String} :
  fisHex s.toLower = fisHex s.toUpper :=
sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval fisHex "redlionfish"

/-
info: 1
-/
-- #guard_msgs in
-- #eval fisHex "Aeneus corydoras"

/-
info: 4
-/
-- #guard_msgs in
-- #eval fisHex "blowfish"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible