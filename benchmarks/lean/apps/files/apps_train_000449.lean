-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def character_replacement (s : String) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem character_replacement_basic_properties
  (s : String) (k : Nat) :
  let result := character_replacement s k
  -- Result bounded by string length
  result ≤ s.length ∧
  -- For non-empty strings, result at least min(len(s), k+1)
  (s ≠ "" → result ≥ min s.length (k+1)) ∧
  -- Empty string returns 0
  (s = "" → result = 0) ∧
  -- If k ≥ length, result equals length
  (k ≥ s.length → result = s.length) :=
  sorry

theorem character_replacement_empty
  (k : Nat) :
  character_replacement "" k = 0 :=
  sorry

theorem character_replacement_monotonic
  (s : String) (k : Nat) :
  s ≠ "" →
  character_replacement s k ≤ character_replacement s (k + 1) :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval character_replacement "ABAB" 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval character_replacement "AABABBA" 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval character_replacement "" 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible