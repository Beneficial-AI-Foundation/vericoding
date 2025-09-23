-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def drop_cap (s : String) : String := sorry

theorem empty_and_whitespace (s : String) :
  (s.isEmpty → (drop_cap s).isEmpty) ∧ 
  (¬s.isEmpty → (drop_cap s).length ≥ s.trim.length) := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spacing_preserved (s : String) (h : ¬s.isEmpty) :
  let orig_spaces := s.split (λ c => c.isWhitespace)
  let result_spaces := (drop_cap s).split (λ c => c.isWhitespace)
  orig_spaces.map (λ s => s.length) = result_spaces.map (λ s => s.length) := by sorry

theorem edge_cases (s : String) :
  (s.trim.length ≤ 2 → drop_cap s = s) ∧
  (s.trim.length > 2 → drop_cap s = s.toLower.capitalize) := by sorry

theorem uppercase_words (s : String) 
  (h₁ : s.length ≥ 3)
  (h₂ : ∀ c ∈ s.data, 65 ≤ c.toNat ∧ c.toNat ≤ 90) :
  drop_cap s = s.toLower.capitalize := by sorry
-- </vc-theorems>