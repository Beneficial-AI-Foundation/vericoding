-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry

def divisors (n : Nat) : Option (List Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisors_properties (n : Nat) (h : n ≥ 2) :
  match (divisors n) with
  | some lst => 
    -- Each divisor divides n
    (∀ d ∈ lst, n % d = 0) ∧
    -- Divisors are ordered
    (∀ i < lst.length - 1, lst.get ⟨i, sorry⟩ ≤ lst.get ⟨i+1, sorry⟩) ∧
    -- Divisors are proper (less than n)
    (∀ d ∈ lst, d < n) ∧
    -- Divisors are greater than 1
    (∀ d ∈ lst, d > 1)
  | none =>
    -- n is prime 
    ∀ i : Nat, 2 ≤ i → i ≤ sqrt n → n % i ≠ 0
  := sorry
-- </vc-theorems>