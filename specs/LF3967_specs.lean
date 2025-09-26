-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime : Nat → Bool :=
sorry

def factorial (n : Nat) : Nat :=
sorry

def factors_up_to (n : Nat) (k : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem not_prime_if_less_than_2 (n : Nat) (h : n ≤ 1) : ¬(is_prime n = true) :=
sorry

theorem prime_iff_no_factors (n : Nat) (h : n ≥ 2) :
  is_prime n = true ↔ ¬(factors_up_to n (n/2) = true) :=
sorry

theorem wilson_prime_property (n : Nat) (h1 : n ≥ 2) (h2 : n ≤ 20) :
  is_prime n = true → (factorial (n-1) + 1) % n = 0 :=
sorry
-- </vc-theorems>