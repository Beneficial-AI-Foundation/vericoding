-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_distance (n : Nat) (fuel : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_zero_distance_zero (n : Nat) (fuel : List Nat) (h : fuel.length > 0) :
  fuel.get ⟨0, h⟩ = 0 → find_distance n fuel = 0 :=
sorry

theorem all_zeros_distance_zero (n : Nat) :
  find_distance n (List.replicate n 0) = 0 :=
sorry

theorem single_nonzero_distance (n : Nat) (val : Nat) (h : n > 0) :
  find_distance n (val :: List.replicate (n-1) 0) = val :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_distance 5 [3, 0, 0, 0, 0]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_distance 5 [1, 1, 1, 1, 1]

/-
info: 15
-/
-- #guard_msgs in
-- #eval find_distance 5 [5, 4, 3, 2, 1]
-- </vc-theorems>