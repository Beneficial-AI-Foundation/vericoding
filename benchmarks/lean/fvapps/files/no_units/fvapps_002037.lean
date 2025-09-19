-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_toy_train (n : Nat) (pairs : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_toy_train_length {n : Nat} {pairs : List (Nat × Nat)} 
  (h : n ≥ 2) :
  (solve_toy_train n pairs).length = n :=
sorry

theorem solve_toy_train_nonnegative {n : Nat} {pairs : List (Nat × Nat)} 
  (h : n ≥ 2) :
  ∀ x, x ∈ solve_toy_train n pairs → x ≥ 0 :=
sorry

theorem solve_toy_train_bounded_difference {n : Nat} {pairs : List (Nat × Nat)}
  (h : n ≥ 2) :
  let result := solve_toy_train n pairs
  ∀ i j, i ∈ List.range result.length → j ∈ List.range result.length →
    result[i]! - result[j]! ≤ n :=
sorry

theorem solve_toy_train_empty {n : Nat}
  (h : n ≥ 2) :
  let result := solve_toy_train n []
  result.length = n ∧ ∀ x, x ∈ result → x = 0 :=
sorry

theorem solve_toy_train_self_loops {n : Nat}
  (h : n ≥ 2) :
  let pairs := List.range n |>.map (fun i => (i+1, i+1))
  let result := solve_toy_train n pairs
  result.length = n ∧ 
  ∀ i j, i ∈ List.range result.length → j ∈ List.range result.length →
    result[i]! = result[j]! :=
sorry
-- </vc-theorems>