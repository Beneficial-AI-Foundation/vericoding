-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat :=
  sorry

def lcm (a b : Nat) : Nat :=
  sorry

def find_gcd_lcm_pairs (pairs : List (Nat × Nat)) : List (Nat × Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_divides {x y : Nat} (h1 : x > 0) (h2 : y > 0) :
  let g := gcd x y
  x % g = 0 ∧ y % g = 0 :=
sorry

theorem lcm_dividedby {x y : Nat} (h1 : x > 0) (h2 : y > 0) :
  let l := lcm x y
  l % x = 0 ∧ l % y = 0 :=
sorry

theorem gcd_lcm_product {x y : Nat} (h1 : x > 0) (h2 : y > 0) :
  gcd x y * lcm x y = x * y :=
sorry

theorem gcd_upper_bound {x y : Nat} (h1 : x > 0) (h2 : y > 0) :
  gcd x y ≤ min x y :=
sorry

theorem lcm_lower_bound {x y : Nat} (h1 : x > 0) (h2 : y > 0) :
  lcm x y ≥ max x y :=
sorry

theorem same_number_gcd_lcm {n : Nat} (h : n > 0) :
  gcd n n = n ∧ lcm n n = n :=
sorry

theorem find_gcd_lcm_pairs_preserves_length {pairs : List (Nat × Nat)} :
  pairs.length = (find_gcd_lcm_pairs pairs).length :=
sorry
-- </vc-theorems>