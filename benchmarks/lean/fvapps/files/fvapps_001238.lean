-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_sum (l r : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_sum_range_bounds (l r : Nat)
  (h1 : 1 ≤ l) (h2 : l ≤ r) (h3 : r ≤ 1000) : 
  0 ≤ calculate_sum l r ∧ calculate_sum l r ≤ 1000000007 :=
  sorry

theorem calculate_sum_identity (n : Nat)
  (h : 1 ≤ n ∧ n ≤ 1000) :
  calculate_sum n n = n :=
  sorry 

theorem calculate_sum_commutative (l r : Nat)
  (h1 : 1 ≤ l) (h2 : l ≤ r) (h3 : r ≤ 1000) :
  calculate_sum l r = calculate_sum l r :=
  sorry

theorem calculate_sum_consecutive (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 100) :
  calculate_sum n (n + 1) = (n + (n &&& (n + 1))) % 1000000007 :=
  sorry
-- </vc-theorems>