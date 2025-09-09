-- <vc-helpers>
-- </vc-helpers>

def is_tune (notes: List Int) : Bool := sorry

theorem empty_list_not_tune : 
  ∀ (notes: List Int), 
  notes = [] → ¬ is_tune notes := sorry

theorem shifted_notes_preserve_tune :
  ∀ (notes: List Int),
  notes ≠ [] →
  is_tune notes = is_tune (notes.map (· + 12)) := sorry

theorem major_scale_subset_is_tune :
  ∀ (notes: List Int),
  notes ≠ [] →
  (∀ n ∈ notes, n % 12 ∈ [0, 2, 4, 5, 7, 9, 11]) →
  is_tune notes := sorry

theorem modulo_12_preserves_tune :
  ∀ (notes: List Int),
  notes ≠ [] →
  is_tune notes = is_tune (notes.map (· % 12)) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_tune [1, 3, 6, 8, 10, 12]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_tune [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_tune [2, 4, 7, 9, 11, 13]

-- Apps difficulty: introductory
-- Assurance level: unguarded