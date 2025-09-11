-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_ops (n x m : Nat) (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_array_ops_preserves_input (n x m : Nat) (arr : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : 1 ≤ x ∧ x ≤ n)
  (h3 : 0 ≤ m ∧ m ≤ 100) :
  let arr' := arr
  solve_array_ops n x m arr = solve_array_ops n x m arr' :=
sorry

theorem solve_array_ops_zero_m (n x : Nat) (arr : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100) 
  (h2 : 1 ≤ x ∧ x ≤ n)
  (h3 : arr.length ≥ n) :
  solve_array_ops n x 0 arr = arr[x-1]! :=
sorry

theorem solve_array_ops_equivalent_ops (n x m : Nat) (arr : List Nat)
  (h1 : 1 ≤ n ∧ n ≤ 100)
  (h2 : 1 ≤ x ∧ x ≤ n)
  (h3 : 0 ≤ m ∧ m ≤ 100) :
  solve_array_ops n x m arr = solve_array_ops n x (m + 0) arr :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_array_ops 3 2 3 [1, 2, 3]

/-
info: 15
-/
-- #guard_msgs in
-- #eval solve_array_ops 3 3 3 [1, 2, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_array_ops 2 2 2 [1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible