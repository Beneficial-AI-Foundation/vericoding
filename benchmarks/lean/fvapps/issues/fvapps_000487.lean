-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rob_houses (nums: List Nat) : Nat := sorry

theorem rob_houses_non_negative (nums: List Nat) :
  rob_houses nums ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rob_houses_maximum_possible (nums: List Nat) :
  rob_houses nums ≤ List.sum nums := sorry 

theorem rob_houses_empty :
  rob_houses [] = 0 := sorry

theorem rob_houses_single (x: Nat) :
  rob_houses [x] = x := sorry

theorem rob_houses_two_equal (x: Nat) :
  rob_houses [x, x] = x := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval rob_houses [2, 3, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval rob_houses [1, 2, 3, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval rob_houses [1]
-- </vc-theorems>