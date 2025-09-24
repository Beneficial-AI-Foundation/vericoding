-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ship_within_days (weights : List Nat) (days : Nat) : Nat := sorry

theorem ship_within_days_one_day (weights : List Nat) 
  (h : weights ≠ []) :
  ship_within_days weights 1 = List.sum weights :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ship_within_days_max_days (weights : List Nat)
  (h : weights ≠ []) :
  ship_within_days weights (List.length weights) ≥ (List.maximum? weights).getD 0 :=
  sorry

theorem ship_within_days_monotonic (weights : List Nat) 
  (d1 d2 : Nat)
  (h1 : List.length weights ≥ 2)
  (h2 : d1 ≤ d2) :
  ship_within_days weights d1 ≥ ship_within_days weights d2 :=
  sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval ship_within_days [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 5

/-
info: 6
-/
-- #guard_msgs in
-- #eval ship_within_days [3, 2, 2, 4, 1, 4] 3

/-
info: 3
-/
-- #guard_msgs in
-- #eval ship_within_days [1, 2, 3, 1, 1] 4
-- </vc-theorems>