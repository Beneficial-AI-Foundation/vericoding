def sumList : List Int → Int 
  | [] => 0
  | (x::xs) => x + sumList xs

def lengthList : List Int → Int
  | [] => 0
  | (_::xs) => 1 + lengthList xs

-- <vc-helpers>
-- </vc-helpers>

def better_than_average (class_points: List Int) (your_points: Int) : Bool :=
  sorry

theorem better_than_average_spec {class_points: List Int} {your_points: Int}
  (h: class_points ≠ []) :
  better_than_average class_points your_points = 
    (your_points > (sumList class_points / lengthList class_points)) :=
  sorry

theorem better_than_average_edge_cases1 :
  better_than_average [0] 0 = false :=
  sorry

theorem better_than_average_edge_cases2 :
  better_than_average [1] 1 = false :=
  sorry

theorem better_than_average_edge_cases3 :
  better_than_average [0] 1 = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval better_than_average [2, 3] 5

/-
info: True
-/
-- #guard_msgs in
-- #eval better_than_average [100, 40, 34, 57, 29, 72, 57, 88] 75

/-
info: True
-/
-- #guard_msgs in
-- #eval better_than_average [12, 23, 34, 45, 56, 67, 78, 89, 90] 69

-- Apps difficulty: introductory
-- Assurance level: unguarded