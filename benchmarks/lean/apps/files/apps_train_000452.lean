def countServers (grid : List (List Nat)) : Nat := sorry

def is_valid_grid (grid : List (List Nat)) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def count_ones (grid : List (List Nat)) : Nat := sorry

theorem countServers_non_negative (grid : List (List Nat)) :
  is_valid_grid grid → countServers grid ≥ 0 := sorry

theorem countServers_upper_bound (grid : List (List Nat)) :
  is_valid_grid grid → countServers grid ≤ count_ones grid := sorry

theorem single_server_result (grid : List (List Nat)) :
  is_valid_grid grid → count_ones grid = 1 → countServers grid = 0 := sorry

theorem empty_grid_zero {m n : Nat} (grid : List (List Nat)) :
  m > 0 → n > 0 → 
  grid = List.replicate m (List.replicate n 0) →
  countServers grid = 0 := sorry

theorem full_grid_count {n : Nat} (grid : List (List Nat)) :
  n ≥ 2 →
  grid = List.replicate n (List.replicate n 1) →
  countServers grid = n * n := sorry

theorem diagonal_only_zero {n : Nat} (grid : List (List Nat)) :
  n ≥ 2 →
  grid = List.map 
    (fun i => List.map (fun j => if i = j then 1 else 0) (List.range n)) 
    (List.range n) →
  countServers grid = 0 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval countServers [[1, 0], [0, 1]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval countServers [[1, 0], [1, 1]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval countServers [[1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

-- Apps difficulty: interview
-- Assurance level: unguarded