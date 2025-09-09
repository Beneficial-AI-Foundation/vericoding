def List.padRight (default : α) (n : Nat) (xs : List α) : List α :=
  sorry

def find_weird_distance (n : Nat) (alice_speeds : List Nat) (bob_speeds : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def running_sum_equal (alice_speeds bob_speeds : List Nat) : Nat :=
  sorry

theorem identical_speeds_sum_to_length
  (n : Nat)
  (h1 : n > 0)
  (h2 : n ≤ 100) :
  find_weird_distance n (List.replicate n 1) (List.replicate n 1) = n := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_weird_distance 4 [1, 3, 3, 4] [1, 2, 4, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_weird_distance 2 [2, 3] [3, 2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_weird_distance 2 [3, 3] [3, 3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible