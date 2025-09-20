-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insert_missing_letters (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_includes_input (s : String) (c : Char) :
  c ∈ s.data → c ∈ (insert_missing_letters s).data :=
  sorry

theorem length_preserves_or_increases (s : String) :
  (insert_missing_letters s).length ≥ s.length :=
  sorry

theorem result_only_contains_letters (s : String) (c : Char) :
  c ∈ (insert_missing_letters s).data → c.isAlpha :=
  sorry

theorem case_pattern (s : String) (i : String.Pos) (c : Char) :
  c = (insert_missing_letters s).get i →
    (∃ j : String.Pos, j ≤ i ∧ c.toLower = s.get j → c.isLower) ∧
    (¬∃ j : String.Pos, j ≤ i ∧ c.toLower = s.get j → c.isUpper) :=
  sorry

theorem single_letter_z : 
  insert_missing_letters "z" = "z" :=
  sorry

theorem single_letter_a :
  insert_missing_letters "a" = "aBCDEFGHIJKLMNOPQRSTUVWXYZ" :=
  sorry
-- </vc-theorems>