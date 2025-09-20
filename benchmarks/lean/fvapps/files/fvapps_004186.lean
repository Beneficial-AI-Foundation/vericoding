-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Bool :=
  sorry

def end_one (n : Nat) : Bool :=
  sorry

def solve (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_prime_not_small (n : Nat) :
  n ≤ 1 → is_prime n = false :=
sorry

theorem is_prime_no_factors (n : Nat) :
  is_prime n = true →
  ∀ i : Nat, 2 ≤ i → i ≤ n^(1/2) → n % i ≠ 0 :=
sorry

theorem prime_multiplication (n : Nat) :
  2 < n → is_prime (2*n) = false :=
sorry

theorem end_one_is_bool (n : Nat) :
  end_one n = true ∨ end_one n = false :=
sorry

theorem end_one_for_one :
  end_one 1 = true :=
sorry

theorem end_one_special_cases (n : Nat) :
  (n = 1 ∨ n = 10) → end_one n = true :=
sorry

theorem solve_bounded (a b : Nat) :
  a ≤ b →
  0 ≤ solve a b ∧ solve a b ≤ b - a :=
sorry

theorem solve_wrong_order (a b : Nat) :
  b < a → solve a b = 0 :=
sorry

theorem solve_unit_range (n : Nat) :
  solve n (n+1) = 0 ∨ solve n (n+1) = 1 :=
sorry
-- </vc-theorems>