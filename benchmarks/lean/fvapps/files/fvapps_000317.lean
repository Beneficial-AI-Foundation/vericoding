-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_zigzag (s : String) (numRows : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zigzag_properties {s : String} {numRows : Nat} 
  (h1 : s.length > 0) (h2 : numRows > 0) (h2a : numRows ≤ 100) :
  let result := convert_zigzag s numRows
  (result.length = s.length) :=
sorry

theorem single_row_is_identity {s : String} (h : s.length > 0) :
  convert_zigzag s 1 = s :=
sorry

theorem first_char_pattern {s : String} {numRows : Nat}
  (h1 : s.length ≥ numRows) (h2 : numRows > 1) (h3 : numRows ≤ 100) :
  let result := convert_zigzag s numRows
  result.get 0 = s.get 0 :=
sorry

theorem empty_string_identity {s : String} {n : Nat}
  (h1 : s.length = 0) (h2 : n > 0) (h3 : n < 4) :
  convert_zigzag s n = s :=
sorry

theorem single_char_identity {s : String} {n : Nat}
  (h1 : s.length = 1) (h2 : n > 0) (h3 : n < 4) :
  convert_zigzag s n = s := 
sorry
-- </vc-theorems>