-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_col_triang (points : List Point) : TriangleCount :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_col_triang_basic_properties {points : List Point} :
  let result := count_col_triang points;
  result.totalPoints = points.length ∧ 
  result.uniqueColors ≤ result.totalPoints ∧
  result.triangleCount ≥ 0 := by sorry

theorem count_col_triang_max_info {points : List Point} :
  let result := count_col_triang points;
  (result.maxColorInfo = none → result.triangleCount = 0) ∧
  (result.maxColorInfo.isSome → 
    match result.maxColorInfo with
    | some (colors, count) => count > 0 ∧ colors.eraseDups = colors
    | none => True) := by sorry 

theorem count_col_triang_vertical_collinear {points : List Point} 
    (h : ∀ p ∈ points, p.coord.1 = 1) :
  let result := count_col_triang points;
  result.triangleCount = 0 ∧ result.maxColorInfo = none := by sorry

theorem count_col_triang_horizontal_collinear {points : List Point}
    (h : ∀ p ∈ points, p.coord.2 = 1) :
  let result := count_col_triang points;
  result.triangleCount = 0 ∧ result.maxColorInfo = none := by sorry

/-
info: [10, 3, 11, ['red', 10]]
-/
-- #guard_msgs in
-- #eval count_col_triang [[[3, -4], "blue"], [[-7, -1], "red"], [[7, -6], "yellow"], [[2, 5], "yellow"], [[1, -5], "red"], [[-1, 4], "red"], [[1, 7], "red"], [[-3, 5], "red"], [[-3, -5], "blue"], [[4, 1], "blue"]]

/-
info: [10, 3, 7, ['red', 6]]
-/
-- #guard_msgs in
-- #eval count_col_triang [[[3, -4], "blue"], [[-7, -1], "red"], [[7, -6], "yellow"], [[2, 5], "yellow"], [[1, -5], "red"], [[1, 1], "red"], [[1, 7], "red"], [[1, 4], "red"], [[-3, -5], "blue"], [[4, 1], "blue"]]

/-
info: [9, 3, 0, []]
-/
-- #guard_msgs in
-- #eval count_col_triang [[[1, -2], "red"], [[7, -6], "yellow"], [[2, 5], "yellow"], [[1, -5], "red"], [[1, 1], "red"], [[1, 7], "red"], [[1, 4], "red"], [[-3, -5], "blue"], [[4, 1], "blue"]]
-- </vc-theorems>