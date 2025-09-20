-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime : Nat → Bool :=
sorry

def reverse : Nat → Nat :=
sorry

def backwards_prime : Nat → Nat → List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem backwards_prime_empty_range :
  backwards_prime 1 0 = [] ∧
  backwards_prime 0 1 = [] :=
sorry
-- </vc-theorems>