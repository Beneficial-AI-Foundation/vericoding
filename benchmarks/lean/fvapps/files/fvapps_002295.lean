-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def subtract_product_and_sum (n : Nat) : Int :=
sorry

def digits (n : Nat) : List Nat :=
sorry

def product_of_list (l : List Nat) : Nat :=
sorry

def sum_of_list (l : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_zero (n : Nat) (h : n > 0 ∧ n < 10) :
  subtract_product_and_sum n = 0 :=
sorry

theorem three_digit_bounds (n : Nat) (h : n ≥ 100 ∧ n ≤ 999) :
  subtract_product_and_sum n ≤ 729 ∧ subtract_product_and_sum n ≥ -27 :=
sorry
-- </vc-theorems>