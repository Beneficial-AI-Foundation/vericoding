-- <vc-helpers>
-- </vc-helpers>

def count_manhattan_compass_pairs (n : Nat) (a b : Nat) (points : List (Int × Int)) : Nat :=
sorry

theorem manhattan_compass_property 
  (n : Nat) (a b : Nat) (points : List (Int × Int))
  (h1 : n ≥ 2) 
  (h2 : a > 0)
  (h3 : b > 0)
  (h4 : a ≤ n)
  (h5 : b ≤ n)
  (h6 : a ≠ b)
  (h7 : points.length = n)
  (h8 : points.Nodup) :
  let result := count_manhattan_compass_pairs n a b points
  result ≥ 0 ∧ result ≤ n * (n-1) / 2 :=
sorry

theorem symmetry_property
  (n : Nat) (a b : Nat) (points : List (Int × Int))
  (h1 : n ≥ 2)
  (h2 : a > 0)
  (h3 : b > 0)
  (h4 : a ≤ n)
  (h5 : b ≤ n)
  (h6 : a ≠ b)
  (h7 : points.length = n)
  (h8 : points.Nodup) :
  count_manhattan_compass_pairs n a b points = count_manhattan_compass_pairs n b a points :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_manhattan_compass_pairs *test1

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_manhattan_compass_pairs *test2

/-
info: 7
-/
-- #guard_msgs in
-- #eval count_manhattan_compass_pairs *test3

-- Apps difficulty: competition
-- Assurance level: unguarded