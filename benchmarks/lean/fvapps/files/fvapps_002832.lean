-- <vc-preamble>
structure IsSorted (xs : List Nat) : Prop where
  sorted : ∀ i j, i < xs.length → j < xs.length → i ≤ j → xs[i]! ≤ xs[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat :=
sorry

def is_prime (n : Nat) : Bool :=
sorry

def prime_factors_sum (n : Nat) : Nat :=
sorry

def divisors_sum (n : Nat) : Nat :=
sorry

def ds_multof_pfs (nMin nMax : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_prime_properties {n : Nat} :
  (n < 2 → is_prime n = false) ∧
  (is_prime n = true → n ≥ 2) ∧
  (is_prime n = true → ∀ i : Nat, 2 ≤ i ∧ i ≤ sqrt n → n % i ≠ 0) :=
sorry

theorem prime_factors_sum_properties {n : Nat} (h : n ≥ 2) :
  prime_factors_sum n > 0 ∧
  prime_factors_sum n ≤ n * n :=
sorry

theorem ds_multof_pfs_properties {nMin nMax : Nat} (h : nMin ≤ nMax) :
  let result := ds_multof_pfs nMin nMax
  IsSorted result ∧
  (∀ x ∈ result, nMin ≤ x ∧ x ≤ nMax) ∧
  (∀ n ∈ result, prime_factors_sum n > 0 ∧ (divisors_sum n) % (prime_factors_sum n) = 0) ∧
  (∀ i j, i < result.length → j < result.length → i ≠ j → result[i]! ≠ result[j]!) :=
sorry
-- </vc-theorems>