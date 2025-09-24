-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_division3_contests (N K D : Nat) (A : List Nat) : Nat := sorry

theorem result_bounded_by_D (N K D : Nat) (A : List Nat) (h1 : N ≥ 1) (h2 : K ≥ 1) (h3 : D ≥ 1) :
  solve_division3_contests N K D A ≤ D := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_nonnegative (N K D : Nat) (A : List Nat) (h1 : N ≥ 1) (h2 : K ≥ 1) (h3 : D ≥ 1) :
  solve_division3_contests N K D A ≥ 0 := sorry

theorem zero_days_gives_zero (N K : Nat) (A : List Nat) (h1 : N ≥ 1) (h2 : K ≥ 1) :
  solve_division3_contests N K 0 A = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_division3_contests 1 5 31 [4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_division3_contests 1 10 3 [23]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_division3_contests 2 5 7 [20, 36]
-- </vc-theorems>