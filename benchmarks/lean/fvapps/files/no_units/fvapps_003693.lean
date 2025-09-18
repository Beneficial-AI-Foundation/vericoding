-- <vc-preamble>
def phone_number_format (a p l: String) : String :=
  s!"({a}) {p}-{l}"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def area_code (s: String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem area_code_extracts_area_from_standard_format {a p l : String}
  (h1: a.length = 3) (h2: p.length = 3) (h3: l.length = 4) :
  area_code (phone_number_format a p l) = a := by
  sorry

theorem area_code_extracts_area_with_surrounding_text {a p l t1 t2 : String}
  (h1: a.length = 3) (h2: p.length = 3) (h3: l.length = 4) :
  area_code (t1 ++ phone_number_format a p l ++ t2) = a := by
  sorry

theorem area_code_empty_parens :
  area_code "()" = "" := by
  sorry

theorem area_code_nested_parens :
  area_code "(123(456)789)" = "123(456" := by
  sorry
-- </vc-theorems>