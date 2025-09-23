-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_subpattern (s : String) : Bool := sorry

theorem single_char_no_pattern (s : String) :
  s.length = 1 → ¬(has_subpattern s) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem doubled_string_has_pattern (s : String) : 
  s.length > 0 → has_subpattern (s ++ s) := sorry

theorem pattern_preserved_by_repetition (s : String) :
  s.length > 0 → has_subpattern s → 
  (has_subpattern (s ++ s ++ s) ∧ has_subpattern (s ++ s ++ s ++ s)) := sorry

theorem pattern_length_divides_string_length (s : String) :
  s.length > 0 → has_subpattern s → 
  ∃ i : Nat, i > 0 ∧ i ≤ s.length ∧ s.length % i = 0 := sorry
-- </vc-theorems>