-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_to_base7 (n : Int) : String := sorry

def base7_to_decimal (s : String) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_to_base7_negative_sign (x : Int) :
  x < 0 → (convert_to_base7 x).startsWith "-" :=
sorry

theorem convert_to_base7_positive_no_sign (x : Int) :
  x ≥ 0 → ¬(convert_to_base7 x).startsWith "-" :=
sorry

theorem convert_to_base7_roundtrip (x : Int) :
  base7_to_decimal (convert_to_base7 x) = x :=
sorry

theorem convert_to_base7_valid_digits (x : Int) :
  let digits := if (convert_to_base7 x).startsWith "-" then (convert_to_base7 x).drop 1 else convert_to_base7 x
  ∀ d, d ∈ digits.data → d ∈ ['0', '1', '2', '3', '4', '5', '6'] :=
sorry

theorem convert_to_base7_single_digit (x : Int) :
  0 ≤ x → x ≤ 6 → convert_to_base7 x = toString x :=
sorry
-- </vc-theorems>