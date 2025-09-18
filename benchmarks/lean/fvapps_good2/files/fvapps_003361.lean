-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def morse_converter (s : String) : Nat :=
  sorry

def convertToMorse (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem morse_converter_output_valid (s : String) :
  let result := morse_converter s
  result ≥ 0
  :=
sorry
-- </vc-theorems>