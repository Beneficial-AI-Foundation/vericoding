-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_make_equal (s t : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem can_make_equal_reflexive (s : String) (h : s.length > 0) :
  can_make_equal s s = true :=
sorry

theorem can_make_equal_length_mismatch (s t : String) (h₁ : s.length > 0) (h₂ : t.length > 0) :
  s.length ≠ t.length → can_make_equal s t = false :=
sorry

theorem can_make_equal_character_sets (s t : String) (h₁ : s.length > 0) (h₂ : t.length > 0) :
  s.length = t.length → 
  (∃ c, c ∈ s.data ↔ c ∉ t.data) →
  can_make_equal s t = false :=
sorry

theorem can_make_equal_symmetric (s t : String) (h₁ : s.length > 0) (h₂ : t.length > 0) :
  s.length = t.length →
  can_make_equal s t = can_make_equal t s :=
sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval can_make_equal "abcd" "abdc"

/-
info: True
-/
-- #guard_msgs in
-- #eval can_make_equal "ababa" "baaba"

/-
info: True
-/
-- #guard_msgs in
-- #eval can_make_equal "abcd" "badc"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded