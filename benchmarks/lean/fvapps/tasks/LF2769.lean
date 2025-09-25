-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_tune (notes: List Int) : Bool := sorry

theorem empty_list_not_tune : 
  ∀ (notes: List Int), 
  notes = [] → ¬ is_tune notes := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>