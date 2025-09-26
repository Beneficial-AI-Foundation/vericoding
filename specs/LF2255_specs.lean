-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (h::t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_min_cost_trip (n m a b c : Nat) (prices : List Nat) (edges : List (Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_min_cost_trip_non_negative (n m a b c : Nat) (prices : List Nat) 
    (edges : List (Nat × Nat)) : 
    solve_min_cost_trip n m a b c prices edges ≥ 0 :=
sorry

theorem solve_min_cost_trip_bounded (n m a b c : Nat) (prices : List Nat)
    (edges : List (Nat × Nat)) :
    solve_min_cost_trip n m a b c prices edges ≤ 
    (List.take m prices).sum :=
sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_min_cost_trip 4 3 2 3 4 [1, 2, 3] [(1, 2), (1, 3), (1, 4)]

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve_min_cost_trip 7 9 1 5 7 [2, 10, 4, 8, 5, 6, 7, 3, 3] [(1, 2), (1, 3), (1, 4), (3, 2), (3, 5), (4, 2), (5, 6), (1, 7), (6, 7)]
-- </vc-theorems>