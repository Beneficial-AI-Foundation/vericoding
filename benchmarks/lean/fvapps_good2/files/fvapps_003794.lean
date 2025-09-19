-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strong_num (n : Nat) : String :=
sorry

def factorial (n : Nat) : Nat :=
sorry

def sumDigitFactorials (n : Nat) : Nat :=
sorry

def digitsOfNat (n : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strong_num_outputs_valid_string (n : Nat) :
  (strong_num n = "STRONG!!!!" ∨ strong_num n = "Not Strong !!") :=
sorry

theorem strong_num_correctness (n : Nat) :
  (strong_num n = "STRONG!!!!" ↔ sumDigitFactorials n = n) :=
sorry

theorem single_digit_strong_nums (n : Nat) :
  n ≤ 9 →
  (strong_num n = "STRONG!!!!" ↔ (n = 1 ∨ n = 2)) :=
sorry

theorem digit_composition_property (digits : List Nat) :
  (∀ d ∈ digits, d ≤ 9) →
  let n := sorry
  (strong_num n = "STRONG!!!!" ↔ (sumDigitFactorials n = n)) :=
sorry
-- </vc-theorems>