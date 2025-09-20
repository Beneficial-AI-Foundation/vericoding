-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lcm_cardinality (n : Nat) : Nat :=
sorry

def lcm (a b : Nat) : Nat :=
sorry

def divisors (n : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lcm_cardinality_positive (n : Nat) (h : n ≥ 1) :
  lcm_cardinality n ≥ 1 :=
sorry

theorem lcm_cardinality_upper_bound (n : Nat) (h : n ≥ 1) :
  let divs := List.length (divisors n)
  lcm_cardinality n ≤ 1 + (divs * (divs - 1)) / 2 :=
sorry

theorem lcm_cardinality_monotonic_powers_two (i : Nat) (h : i > 0) :
  lcm_cardinality (2^i) ≥ lcm_cardinality (2^(i-1)) :=
sorry

theorem lcm_factors_bound (n : Nat) (h : n ≥ 1) :
  ∀ (a b : Nat), a ∈ divisors n → b ∈ divisors n → lcm a b ≤ n :=
sorry
-- </vc-theorems>