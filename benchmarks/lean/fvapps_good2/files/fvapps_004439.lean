-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_tenth_digit (digits : List Nat) : Nat :=
sorry

def calculate_last_digit (digits : List Nat) : Nat :=
sorry

def check_valid_tr_number (n : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_length_returns_false (n : String) :
  n.length ≠ 11 → check_valid_tr_number n = false :=
sorry

theorem valid_number_is_accepted {digits : List Nat} (h1 : digits.length = 9)
  (h2 : digits.head! ≠ 0) :
  let tenth := calculate_tenth_digit digits
  let full_digits := digits ++ [tenth]
  let last := calculate_last_digit full_digits
  check_valid_tr_number (toString (full_digits ++ [last])) = true :=
sorry

theorem invalid_check_digits_returns_false {n : String} (h1 : n.length = 11) :
  let digits := n.toList.map (·.toString.toNat!)
  digits[9]! ≠ calculate_tenth_digit (digits.take 9) ∨
  digits[10]! ≠ calculate_last_digit (digits.take 10) →
  check_valid_tr_number n = false :=
sorry

theorem invalid_type_returns_false (n : String) :
  ¬(∀ c : Char, c ∈ n.data → c.isDigit) →
  check_valid_tr_number n = false :=
sorry
-- </vc-theorems>