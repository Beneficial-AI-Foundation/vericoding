def min_banana_speed (pile_count : Nat) (hours : Nat) (piles : List Nat) : Nat :=
  sorry

def list_maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs

def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + list_sum xs

-- <vc-helpers>
-- </vc-helpers>

def nat_ceil_div (a b : Nat) : Nat :=
  (a + b - 1) / b

theorem edge_cases_singleton_one :
  min_banana_speed 1 1 [1] = 1 :=
  sorry

theorem edge_cases_singleton_hundred :
  min_banana_speed 1 1 [100] = 100 :=
  sorry

theorem edge_cases_two_ones :
  min_banana_speed 2 2 [1, 1] = 1 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_banana_speed 3 3 [1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_banana_speed 3 4 [1, 2, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_banana_speed 4 5 [4, 3, 2, 7]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible