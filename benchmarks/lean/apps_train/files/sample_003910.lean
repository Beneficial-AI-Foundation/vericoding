/-
A pair of numbers has a unique LCM but a single number can be the LCM of more than one possible
pairs. For example `12` is the LCM of `(1, 12), (2, 12), (3,4)` etc. For a given positive integer N, the number of different integer pairs with LCM is equal to N can be called the LCM cardinality of that number N. In this kata your job is to find out the LCM cardinality of a number.
-/

def lcm_cardinality (n : Nat) : Nat := sorry
def lcm (a b : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def divisors (n : Nat) : List Nat := sorry

theorem lcm_cardinality_positive (n : Nat) (h : n ≥ 1) : 
  lcm_cardinality n ≥ 1 := sorry

theorem lcm_cardinality_upper_bound (n : Nat) (h : n ≥ 1) :
  let divs := List.length (divisors n)
  lcm_cardinality n ≤ 1 + (divs * (divs - 1)) / 2 := sorry

theorem lcm_cardinality_monotonic_powers_two (i : Nat) (h : i > 0) :
  lcm_cardinality (2^i) ≥ lcm_cardinality (2^(i-1)) := sorry

theorem lcm_factors_bound (n : Nat) (h : n ≥ 1) :
  ∀ (a b : Nat), a ∈ divisors n → b ∈ divisors n → lcm a b ≤ n := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible