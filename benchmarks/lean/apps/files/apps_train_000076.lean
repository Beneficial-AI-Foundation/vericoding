-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_fence (heights costs : List Nat) : Nat := sorry

def sum : List Nat → Nat
  | [] => 0
  | (x::xs) => x + sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem solve_fence_non_negative (heights costs : List Nat) :
  solve_fence heights costs ≥ 0 := sorry

theorem solve_fence_empty_or_single (heights costs : List Nat)
  (h : heights.length ≤ 1) :
  solve_fence heights costs = 0 := sorry

theorem solve_fence_cost_bound (heights costs : List Nat) :
  solve_fence heights costs ≤ sum (costs.map (fun c => c * 2)) := sorry

theorem solve_fence_trivial_cases_zero :
  solve_fence [] [] = 0 := sorry

theorem solve_fence_trivial_cases_one (h c : Nat) :
  solve_fence [h] [c] = 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_fence [2, 2, 3] [4, 1, 5]

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_fence [2, 2, 2] [3, 10, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_fence [1, 3, 2, 1000000000] [7, 3, 6, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded