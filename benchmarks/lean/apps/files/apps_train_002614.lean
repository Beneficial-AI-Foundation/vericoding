-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_rect_triang (points : List (Int × Int)) : Nat := sorry

theorem result_properties {points : List (Int × Int)}
    (h : points.length ≥ 3) :
    let n := points.length
    0 ≤ count_rect_triang points ∧ 
    count_rect_triang points ≤ n * (n - 1) * (n - 2) / 6 := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem known_right_triangle :
    count_rect_triang [(0,0), (0,3), (4,0)] = 1 := by sorry

theorem duplicate_handling {points : List (Int × Int)} :
    count_rect_triang points = count_rect_triang (List.eraseDups points) := by sorry

theorem order_invariance {points : List (Int × Int)}
    (h : points.length ≥ 3) :
    count_rect_triang points = count_rect_triang points.reverse := by sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_rect_triang [[1, 2], [3, 3], [4, 1], [1, 1], [4, -1]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_rect_triang [[1, 2], [4, -1], [3, 3], [4, -1], [4, 1], [1, 1], [4, -1], [4, -1], [3, 3], [1, 2]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_rect_triang [[0, 0], [1, 1], [2, 2]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded