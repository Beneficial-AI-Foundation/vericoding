def isValidPolygon (vertices: List (Int × Int)) : Bool := sorry

/- Signature for the main function -/

-- <vc-helpers>
-- </vc-helpers>

def calculateMinCost (vertices: List (Int × Int)) (stripes: List (Float × Int)) : Nat := sorry

theorem min_cost_positive (vertices: List (Int × Int)) (stripes: List (Float × Int))
  (h1: isValidPolygon vertices = true)
  (h2: stripes.length > 0) :
  calculateMinCost vertices stripes > 0 := sorry

theorem min_cost_integer (vertices: List (Int × Int)) (stripes: List (Float × Int))
  (h1: isValidPolygon vertices = true)
  (h2: stripes.length > 0) :
  ∃ n: Nat, calculateMinCost vertices stripes = n := sorry

theorem empty_stripes_error (vertices: List (Int × Int))
  (h1: isValidPolygon vertices = true) :
  ∀ result, calculateMinCost vertices [] ≠ result := sorry

/-
info: 50
-/
-- #guard_msgs in
-- #eval calculate_min_cost [(0, 0), (1000, 0), (1000, 2000), (0, 2000)] [(1000, 10), (2000, 15)]

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_min_cost [(0, 0), (4, 0), (2, 3)] [(5, 2)]

-- Apps difficulty: interview
-- Assurance level: guarded