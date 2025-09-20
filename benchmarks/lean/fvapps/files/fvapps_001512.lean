-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_heavy_bags (size : Nat) (weights : List Nat) : Nat := sorry

theorem count_heavy_bags_bounds (size : Nat) (weights : List Nat) :
  let result := count_heavy_bags size weights
  0 ≤ result ∧ result ≤ weights.length := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>