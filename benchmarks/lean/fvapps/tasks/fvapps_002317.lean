-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isBoomerang (points: List (List Int)) : Bool := sorry

def areCollinear (p1 p2 p3: List Int) : Bool :=
  (p2.get! 1 - p1.get! 1) * (p3.get! 0 - p1.get! 0) == 
  (p3.get! 1 - p1.get! 1) * (p2.get! 0 - p1.get! 0)
-- </vc-definitions>

-- <vc-theorems>
theorem boomerang_collinear_points 
  (points: List (List Int))
  (h1: points.length = 3)
  (h2: ∀ p ∈ points, p.length = 2) :
  areCollinear (points.get! 0) (points.get! 1) (points.get! 2) = true →
  isBoomerang points = false := sorry

theorem boomerang_non_collinear_points
  (points: List (List Int)) 
  (h1: points.length = 3)
  (h2: ∀ p ∈ points, p.length = 2) :
  areCollinear (points.get! 0) (points.get! 1) (points.get! 2) = false →
  isBoomerang points = true := sorry

theorem boomerang_symmetric
  (points: List (List Int))
  (h1: points.length = 3)
  (h2: ∀ p ∈ points, p.length = 2) :
  isBoomerang points = isBoomerang [points.get! 1, points.get! 2, points.get! 0] := sorry

theorem boomerang_duplicate_points
  (points: List (List Int))
  (h1: points.length = 3)
  (h2: ∀ p ∈ points, p.length = 2)
  (h3: points.get! 0 = points.get! 1) :
  isBoomerang points = false := sorry
-- </vc-theorems>