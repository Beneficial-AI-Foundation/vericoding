-- <vc-preamble>
def Coord := Nat × Nat 

def max_distinct_sum (n: Nat) (pairs: List Coord) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + List.sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem max_distinct_sum_single_coord (n: Nat) :
  max_distinct_sum n [(1,n)] = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_distinct_sum 3 [(1, 3), (3, 1), (1, 2)]

/-
info: 11
-/
-- #guard_msgs in
-- #eval max_distinct_sum 5 [(1, 3), (2, 4), (1, 2), (3, 2), (3, 4)]

/-
info: 9
-/
-- #guard_msgs in
-- #eval max_distinct_sum 4 [(1, 1), (2, 2), (3, 3), (4, 4)]
-- </vc-theorems>