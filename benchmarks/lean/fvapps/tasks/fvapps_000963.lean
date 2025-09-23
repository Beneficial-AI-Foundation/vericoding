-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidPolygon (vertices: List (Int × Int)) : Bool :=
sorry

def calculateMinCost (vertices: List (Int × Int)) (stripes: List (Float × Int)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_positive (vertices: List (Int × Int)) (stripes: List (Float × Int))
  (h1: isValidPolygon vertices = true)
  (h2: stripes.length > 0) :
  calculateMinCost vertices stripes > 0 :=
sorry

theorem min_cost_integer (vertices: List (Int × Int)) (stripes: List (Float × Int))
  (h1: isValidPolygon vertices = true)
  (h2: stripes.length > 0) :
  ∃ n: Nat, calculateMinCost vertices stripes = n :=
sorry

theorem empty_stripes_error (vertices: List (Int × Int))
  (h1: isValidPolygon vertices = true) :
  ∀ result, calculateMinCost vertices [] ≠ result :=
sorry
-- </vc-theorems>