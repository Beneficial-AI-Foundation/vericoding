-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sieve (n : Nat) : List Nat :=
sorry

def prime_primes (n : Nat) : Nat × Nat :=
sorry

def is_prime (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sieve_sorted (n : Nat) (h : n ≥ 2) :
  let primes := sieve n
  ∀ i h1 h2, primes.get ⟨i, h1⟩ < primes.get ⟨i+1, h2⟩ :=
sorry

theorem prime_primes_nonneg (n : Nat) (h : n ≥ 2) :
  let (count, total) := prime_primes n
  count ≥ 0 ∧ total ≥ 0 :=
sorry

theorem prime_primes_small_bound (n : Nat) (h : n ≥ 2) (h2 : n ≤ 10) :
  let (count, _) := prime_primes n
  count ≤ n * n / 2 :=
sorry
-- </vc-theorems>