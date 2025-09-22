-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def closest_pair_tonum (n : Nat) : Nat × Nat := sorry

theorem valid_pair_exists (upper_limit : Nat) (h : upper_limit ≥ 30) :
  let (x, y) := closest_pair_tonum upper_limit
  x > y ∧ 
  x < upper_limit ∧ 
  y < upper_limit ∧
  ∃ a b : Nat, x + y = a * a ∧ x - y = b * b :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_pairs_for_small_input (n : Nat) (h : n ≤ 4) :
  ¬∃ x y : Nat, x < n ∧ y < n ∧ x > y ∧
  ∃ a b : Nat, x + y = a * a ∧ x - y = b * b :=
sorry
-- </vc-theorems>