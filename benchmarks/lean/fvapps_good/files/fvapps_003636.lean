-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Nat) : Bool := sorry

def chain_arith_deriv (n : Nat) (k : Nat) : String ⊕ List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chain_length {n k : Nat} (h1 : n ≥ 2) (h2 : k ≥ 1) (h3 : k ≤ 10) :
  let result := chain_arith_deriv n k
  match result with
  | Sum.inl s => ∃ p, isPrime p ∧ s = s!"{p} is a prime number" 
  | Sum.inr l => l.length = k ∧ l.head? = some n
  := sorry

theorem small_primes {p k : Nat} 
  (h1 : p ≥ 2) (h2 : p ≤ 100) (h3 : k ≥ 1) (h4 : k ≤ 10)
  (h5 : isPrime p) :
  chain_arith_deriv p k = Sum.inl s!"{p} is a prime number" := sorry
-- </vc-theorems>