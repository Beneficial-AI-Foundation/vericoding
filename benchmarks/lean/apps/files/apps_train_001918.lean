-- <vc-helpers>
-- </vc-helpers>

def find_max_stars (n : Nat) (a b c d : Int) (stars : List (Int × Int)) : Nat := sorry

theorem output_bounds {n : Nat} {a b c d : Int} {stars : List (Int × Int)}
  (h1 : n > 0) 
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0))
  (h4 : a * d ≠ b * c)
  (h5 : stars ≠ []) :
  let result := find_max_stars n a b c d stars
  result ≥ 0 ∧ result ≤ stars.length := by sorry

theorem identical_points {n : Nat} {a b c d : Int} {stars : List (Int × Int)}
  (h1 : n > 0)
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0)) 
  (h4 : a * d ≠ b * c)
  (h5 : stars ≠ []) :
  find_max_stars n a b c d stars = find_max_stars n a b c d (stars ++ stars) := by sorry

theorem empty_stars {n : Nat} {a b c d : Int}
  (h1 : n > 0)
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0))
  (h4 : a * d ≠ b * c) :
  find_max_stars n a b c d [] = 0 := by sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_max_stars 15 1 3 2 1 [(3, 1), (6, 2), (4, 2), (2, 5), (4, 5), (6, 6), (3, 4), (1, 6), (2, 1), (7, 4), (9, 3), (5, 3), (1, 3), (15, 5), (12, 4)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_stars 5 3 24 24 3 [(31394, 23366), (27990, 71363), (33642, 36903), (79731, 10588), (10907, 5058)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_stars 5 0 17 74 0 [(69711, 29703), (91677, 56040), (26051, 78244), (20816, 40897), (70770, 35908)]

-- Apps difficulty: competition
-- Assurance level: unguarded