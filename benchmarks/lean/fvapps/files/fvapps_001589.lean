-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat :=
sorry

def digits_sorted (n : Nat) : List Nat :=
sorry

def digits_sorted_desc (n : Nat) : List Nat :=
sorry

def next_bigger (n : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_bigger_larger (n : Nat) :
  let result := next_bigger n
  result ≠ -1 → result > n :=
sorry

theorem next_bigger_same_digits (n : Nat) :
  let result := next_bigger n
  result ≠ -1 →
  ∀ (r : Nat), result = r → (digits_sorted n = digits_sorted r) :=
sorry

theorem next_bigger_minimal (n : Nat) :
  let result := next_bigger n
  result ≠ -1 →
  ∀ x, n < x → x < result → digits_sorted x ≠ digits_sorted n :=
sorry

theorem next_bigger_none_exists (n : Nat) :
  next_bigger n = -1 ↔ digits n = digits_sorted_desc n :=
sorry

theorem next_bigger_single_digit (n : Nat) :
  n < 10 → next_bigger n = -1 :=
sorry

theorem next_bigger_output_type (n : Nat) :
  ∃ i : Int, next_bigger n = i :=
sorry
-- </vc-theorems>