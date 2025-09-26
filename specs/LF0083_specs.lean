-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_stack_exterminable (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_stack_exterminable_nonnegative 
  (arr : List Int) 
  (h : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100) 
  (h2 : arr ≠ []) : 
  0 ≤ solve_stack_exterminable arr :=
  sorry

theorem solve_stack_exterminable_reverse_equals_forward
  (arr : List Int)
  (h : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100)
  (h2 : arr ≠ []) :
  solve_stack_exterminable arr = solve_stack_exterminable arr.reverse :=
  sorry

theorem solve_stack_exterminable_pair_elements
  (arr : List Int)
  (h : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100) 
  (h2 : arr.length ≥ 2) :
  let doubled := arr.bind (fun x => [x, x])
  solve_stack_exterminable doubled ≥ arr.length :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_stack_exterminable [2, 1, 1, 2, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_stack_exterminable [1, 2, 1, 1, 3, 2]

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_stack_exterminable [3, 1, 2, 2, 1, 6, 6, 3, 3]
-- </vc-theorems>