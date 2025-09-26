-- <vc-preamble>
def get_primes (n : Nat) (m : Nat := 2) : List (List Nat) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PRIMES : List Nat := sorry

theorem get_primes_length_properties (n m : Nat)
  (h1 : n ≥ 1 ∧ n ≤ 100) (h2 : m ≥ 1 ∧ m ≤ 10) :
  let result := get_primes n m
  -- Total elements ≤ n 
  (result.join.length ≤ n) ∧
  -- Each inner list has length m
  (∀ inner ∈ result, inner.length = m) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_primes_values (n m : Nat)
  (h1 : n ≥ 1 ∧ n ≤ 100) (h2 : m ≥ 1 ∧ m ≤ 10) :  
  let result := get_primes n m
  ∀ x ∈ result.join,
    -- All values are prime 
    x ∈ PRIMES ∧
    -- Values are in ascending order
    (∀ y ∈ result.join, result.join.indexOf y < result.join.indexOf x → y < x) :=
sorry

theorem get_primes_default_m (n : Nat) (h : n ≥ 1 ∧ n ≤ 100) :
  let result := get_primes n
  ∀ inner ∈ result, inner.length = 2 :=
sorry

theorem get_primes_edge_cases :
  get_primes 0 = [] ∧
  get_primes 1 1 = [[2]] ∧ 
  get_primes 1 2 = [[2, 0]] :=
sorry
-- </vc-theorems>