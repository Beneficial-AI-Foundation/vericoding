-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def range_parser (s: String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_parser_correct₁ :
  range_parser "1-10,14,20-25:2" = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 14, 20, 22, 24] :=
  sorry

theorem range_parser_correct₂ :
  range_parser "5-10" = [5, 6, 7, 8, 9, 10] :=
  sorry

theorem range_parser_correct₃ :
  range_parser "2" = [2] :=
  sorry

theorem range_parser_invalid_special_char₁ :
  ∀ s: String,
  s.length = 1 →
  s = " " ∨ s = "," ∨ s = ":" ∨ s = "-" →
  ¬∃ (lst : List Nat), range_parser s = lst :=
  sorry
-- </vc-theorems>