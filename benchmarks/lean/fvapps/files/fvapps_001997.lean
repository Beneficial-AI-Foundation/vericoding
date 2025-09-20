-- <vc-preamble>
def sum_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_robot_energy (n : Nat) (l r ql qr : Nat) (weights : List Nat) : Nat :=
  sorry

-- Result should be non-negative and within bounds
-- </vc-definitions>

-- <vc-theorems>
theorem min_robot_energy_bounds (n : Nat) (l r ql qr : Nat) (weights : List Nat)
    (h1 : n > 0) (h2 : l > 0) (h3 : r > 0) (h4 : weights.length = n) :
    let result := min_robot_energy n l r ql qr weights
    let total_weight := sum_list weights
    result ≥ 0 ∧ 
    result ≥ min l r * total_weight ∧
    result ≤ max l r * total_weight + max ql qr * n :=
  sorry

-- When no penalties, result equals minimum cost times weight sum

theorem min_robot_energy_no_penalties (n : Nat) (l r : Nat) (weights : List Nat)
    (h1 : n > 0) (h2 : l > 0) (h3 : r > 0) (h4 : weights.length = n) :
    min_robot_energy n l r 0 0 weights = min (l * sum_list weights) (r * sum_list weights) :=
  sorry

-- When costs are equal, result is at least sum of weights

theorem min_robot_energy_equal_costs (n : Nat) (ql qr : Nat) (weights : List Nat) 
    (h1 : n > 0) (h2 : weights.length = n) :
    min_robot_energy n 1 1 ql qr weights ≥ sum_list weights :=
  sorry
-- </vc-theorems>