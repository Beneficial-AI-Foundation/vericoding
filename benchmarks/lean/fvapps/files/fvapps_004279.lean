-- <vc-preamble>
def isValidBinaryStr (s : String) : Bool :=
  s.length > 0 && s.all (fun c => c = '0' || c = '1')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def negabinary_to_int (s : String) : Int := sorry

def int_to_negabinary (n : Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem round_trip (n : Int) :
  negabinary_to_int (int_to_negabinary n) = n :=
sorry

theorem valid_binary_string (n : Int) :
  isValidBinaryStr (int_to_negabinary n) :=
sorry

theorem neg_bin_str_converts (s : String) (h : isValidBinaryStr s) :
  ∃ n : Int, negabinary_to_int s = n :=
sorry

theorem zero_special_case :
  int_to_negabinary 0 = "0" :=
sorry
-- </vc-theorems>