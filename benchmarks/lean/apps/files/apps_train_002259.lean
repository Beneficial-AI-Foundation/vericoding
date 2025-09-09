def min_moves_to_equalize (n : Nat) (candies : List Nat) (oranges : List Nat) : Nat :=
  sorry

def list_max (l : List Nat) : Nat :=
  sorry

def list_min (l : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_sum (l : List Nat) : Nat :=
  sorry

theorem min_moves_non_negative (n : Nat) (candies : List Nat) (oranges : List Nat) :
  min_moves_to_equalize n candies oranges ≥ 0 :=
sorry

theorem min_moves_lower_bound (n : Nat) (candies : List Nat) (oranges : List Nat) :
  min_moves_to_equalize n candies oranges ≥ 
    max 
      (list_max candies - list_min candies)
      (list_max oranges - list_min oranges) :=
sorry

theorem min_moves_upper_bound (n : Nat) (candies oranges : List Nat) :
  min_moves_to_equalize n candies oranges ≤ 
    (list_sum (candies.map (λ x => x - list_min candies))) +
    (list_sum (oranges.map (λ x => x - list_min oranges))) :=
sorry

theorem identical_lists_zero_moves (n : Nat) (v : Nat) :
  min_moves_to_equalize n (List.replicate n v) (List.replicate n v) = 0 :=
sorry

theorem min_moves_symmetric (n : Nat) (candies oranges : List Nat) :
  min_moves_to_equalize n candies oranges = min_moves_to_equalize n oranges candies :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval min_moves_to_equalize 3 [3, 5, 6] [3, 2, 3]

/-
info: 16
-/
-- #guard_msgs in
-- #eval min_moves_to_equalize 5 [1, 2, 3, 4, 5] [5, 4, 3, 2, 1]

/-
info: 7
-/
-- #guard_msgs in
-- #eval min_moves_to_equalize 3 [10, 12, 8] [7, 5, 4]

-- Apps difficulty: introductory
-- Assurance level: unguarded