def abs (n : Int) : Nat := 
  if n ≥ 0 then n.toNat else (-n).toNat

def sum (l : List Nat) : Nat :=
  l.foldl (·+·) 0

-- <vc-helpers>
-- </vc-helpers>

def elevator_distance (floors : List Int) : Nat := sorry

theorem elevator_distance_non_negative (floors : List Int) 
  (h : floors.length ≥ 2) : 
  elevator_distance floors ≥ 0 := sorry

theorem elevator_distance_reversal (floors : List Int)
  (h : floors.length ≥ 2) :
  elevator_distance floors = elevator_distance floors.reverse := sorry

theorem elevator_distance_same_floor (n : Int) :
  elevator_distance [n, n] = 0 := sorry

theorem elevator_distance_all_zero (n : Nat) 
  (h : n ≥ 2) :
  elevator_distance (List.replicate n 0) = 0 := sorry

theorem elevator_distance_up_down : 
  elevator_distance [1, -1] = 2 := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval elevator_distance [5, 2, 8]

/-
info: 2
-/
-- #guard_msgs in
-- #eval elevator_distance [1, 2, 3]

/-
info: 18
-/
-- #guard_msgs in
-- #eval elevator_distance [7, 1, 7, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible