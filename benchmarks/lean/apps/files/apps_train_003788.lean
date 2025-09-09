-- <vc-helpers>
-- </vc-helpers>

def nbr_of_laps (x y : Nat) : Nat × Nat := sorry

theorem nbr_of_laps_positive (x y : Nat)
  (h1 : x > 0)
  (h2 : y > 0) :
  let (bob, charles) := nbr_of_laps x y
  bob > 0 ∧ charles > 0 := sorry

theorem nbr_of_laps_equal_distance (x y : Nat)
  (h1 : x > 0)
  (h2 : y > 0) :
  let (bob, charles) := nbr_of_laps x y
  x * bob = y * charles := sorry

theorem nbr_of_laps_same_length (x : Nat)
  (h : x > 0) :
  nbr_of_laps x x = (1, 1) := sorry

/-
info: (3, 5)
-/
-- #guard_msgs in
-- #eval nbr_of_laps 5 3

/-
info: (3, 2)
-/
-- #guard_msgs in
-- #eval nbr_of_laps 4 6

/-
info: (1, 1)
-/
-- #guard_msgs in
-- #eval nbr_of_laps 5 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible