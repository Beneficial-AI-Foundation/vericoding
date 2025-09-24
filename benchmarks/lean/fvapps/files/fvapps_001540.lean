-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divisors (n : Nat) : List Nat := sorry

def isSorted (as : List Nat) : Prop :=
  ∀ i j, i < j → j < as.length → as[i]! ≤ as[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem divisors_properties (n : Nat)
  (h : n > 0 ∧ n ≤ 10000) : 
  let divs := divisors n
  -- All divisors divide n evenly
  ∀ d ∈ divs, n % d = 0
  -- List is sorted
  ∧ isSorted divs
  -- No duplicates 
  ∧ List.Nodup divs
  -- Product of divisor pairs equals n
  ∧ ∀ d ∈ divs, d * d ≤ n → d * (n / d) = n := sorry
-- </vc-theorems>