-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encoder (s : String) : String :=
sorry

def decoder (s : String) : String :=
sorry

def isUpper (c : Char) : Bool :=
sorry

def isDigit (c : Char) : Bool :=
sorry

def startsWithZeroUpper (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encoder_output_format (s : String) (h : s ≠ "") :
  (∀ c, c ∈ s.toList → isDigit c ∨ isUpper c) ∧
  startsWithZeroUpper (encoder s) :=
sorry

theorem encoder_length_bounds (s : String) (h : s ≠ "") :
  String.length (encoder s) ≤ 3 * String.length s ∧
  String.length (encoder s) ≥ String.length s / 2 :=
sorry

theorem encoder_decoder_inverse (s : String) (h : s ≠ "") :
  decoder (encoder s) = s :=
sorry
-- </vc-theorems>