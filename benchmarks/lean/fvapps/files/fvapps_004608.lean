-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_coordinates (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_comma_invalid (s: String) : 
  ¬s.contains ',' → is_valid_coordinates s = false :=
sorry

theorem non_string_types_invalid {α : Type} (x : α) [ToString α] :
  is_valid_coordinates (toString x) = false :=
sorry

theorem out_of_range_latitude_invalid (n : Float) :
  (n < -90 ∨ n > 90) →
  is_valid_coordinates (toString n ++ ", 0") = false :=
sorry

theorem alpha_chars_invalid (s : String) :
  (∃ c ∈ s.data, c.isAlpha) →
  is_valid_coordinates ("0, " ++ s) = false :=
sorry

theorem space_after_minus_invalid :
  is_valid_coordinates "23.234, - 23.4234" = false :=
sorry

theorem multiple_decimals_invalid :
  is_valid_coordinates "23.2.34, 23.4234" = false :=
sorry

theorem scientific_notation_invalid :
  is_valid_coordinates "23e4, 45" = false :=
sorry
-- </vc-theorems>