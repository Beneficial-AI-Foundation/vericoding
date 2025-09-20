-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def duplicateCount (text : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem duplicateCount_nonnegative (text : String) : 
  duplicateCount text ≥ 0 := by
  sorry

theorem duplicateCount_less_than_half_length (text : String) : 
  duplicateCount text ≤ text.length / 2 := by
  sorry

theorem duplicateCount_empty_and_unique (text : String) :
  -- Empty string has no duplicates
  duplicateCount "" = 0 ∧ 
  -- String with only unique chars has no duplicates
  (∀ s : String, (∀ c₁ c₂, c₁ ∈ s.data → c₂ ∈ s.data → c₁ = c₂) → duplicateCount s = 0) := by
  sorry

theorem duplicateCount_repeated_char (c : Char) :
  duplicateCount (String.mk [c, c]) = 1 := by
  sorry
-- </vc-theorems>