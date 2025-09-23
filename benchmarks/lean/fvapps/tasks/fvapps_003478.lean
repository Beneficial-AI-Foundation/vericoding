-- <vc-preamble>
def List.sorted (l : List Nat) : Prop :=
  ∀ i j, i < j → j < l.length →
  match l.get? i, l.get? j with
  | some x, some y => x ≤ y
  | _, _ => true
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def not_primes (start finish : Nat) : List Nat := sorry

def is_prime (n : Nat) : Bool :=
sorry

def all_dig_prime (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem not_primes_empty_for_equal_bounds (n : Nat) :
  not_primes n n = [] :=
sorry

theorem not_primes_empty_for_invalid_range (start finish : Nat)
  (h : finish < start) :
  not_primes start finish = [] :=
sorry
-- </vc-theorems>