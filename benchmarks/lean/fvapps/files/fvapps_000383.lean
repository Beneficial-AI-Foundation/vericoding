-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_ugly_number (n a b c : Nat) : Nat :=
sorry

def gcd (a b : Nat) : Nat :=
sorry

def count_divisible (num a b c : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ugly_number_divisible (n a b c : Nat) (h1 : n > 0) (h2 : a > 0) (h3 : b > 0) (h4 : c > 0) :
  let result := find_nth_ugly_number n a b c
  result % a = 0 ∨ result % b = 0 ∨ result % c = 0 :=
sorry

theorem ugly_number_positive (n a b c : Nat) (h1 : n > 0) (h2 : a > 0) (h3 : b > 0) (h4 : c > 0) :
  find_nth_ugly_number n a b c > 0 :=
sorry

theorem ugly_number_min_bound (n a b c : Nat) (h1 : n > 0) (h2 : a > 0) (h3 : b > 0) (h4 : c > 0) :
  find_nth_ugly_number n a b c ≥ min a (min b c) :=
sorry

theorem ugly_number_max_bound (n a b c : Nat) (h1 : n > 0) (h2 : a > 0) (h3 : b > 0) (h4 : c > 0) :
  find_nth_ugly_number n a b c ≤ n * min a (min b c) :=
sorry

theorem ugly_number_equal_divisors (a : Nat) (h : a > 0) :
  find_nth_ugly_number 1 a a a = a :=
sorry
-- </vc-theorems>