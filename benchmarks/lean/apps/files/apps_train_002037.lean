-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: [10, 9, 10, 10, 9]
-/
-- #guard_msgs in
-- #eval solve_toy_train 5 [(2, 4), (5, 1), (2, 3), (3, 4), (4, 1), (5, 3), (3, 5)]

/-
info: [5, 6]
-/
-- #guard_msgs in
-- #eval solve_toy_train 2 [(1, 2), (1, 2), (1, 2)]

/-
info: [8, 7, 6, 8, 7]
-/
-- #guard_msgs in
-- #eval solve_toy_train 5 [(2, 4), (5, 4), (3, 2)]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible