-- <vc-preamble>
def parse_int (s : String) : Nat :=
  sorry

def normalize_text (s : String) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def int_to_english (n : Nat) : String :=
  sorry

-- Main theorems based on property tests
-- </vc-definitions>

-- <vc-theorems>
theorem parse_int_inverse (n : Nat) (h : n ≤ 999) : 
  parse_int (int_to_english n) = n :=
sorry

theorem parse_int_specific_example :
  parse_int "one hundred twenty three" = 123 :=
sorry
-- </vc-theorems>