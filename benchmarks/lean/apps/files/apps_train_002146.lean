-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_workout (n k : Nat) (x : List Nat) (a : Nat) (c : List Nat) : Int := sorry

def sum_list : List Nat → Nat 
  | [] => 0
  | h::t => h + sum_list t
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_workout_empty (k a : Nat) :
  min_cost_workout 0 k [] a [] = 0 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval min_cost_workout 5 10000 [10000, 30000, 30000, 40000, 20000] 20000 [5, 2, 8, 3, 6]

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_cost_workout 5 10000 [10000, 40000, 30000, 30000, 20000] 10000 [5, 2, 8, 3, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_cost_workout 5 49 [22, 23, 11, 17, 49] 50 [102, 55, 77, 34, 977]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible