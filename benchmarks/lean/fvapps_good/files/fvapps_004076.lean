-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (pattern text : String) : Nat := sorry

theorem pattern_in_text : ∀ (pattern : String) (extra : String), 
  pattern.length > 0 → solve pattern (pattern ++ extra) ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_pattern : ∀ (c : Char) (text : String),
  solve (String.mk [c]) text = (text.data.filter (· = c)).length := sorry

theorem empty_text : ∀ (pattern : String),
  pattern.length > 1 → solve pattern "" = 0 := sorry
-- </vc-theorems>