-- <vc-preamble>
def Point := Float × Float 

structure Datamining where
  points : List Point
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def predict (m : Datamining) (x : Float) : Float := sorry

def abs (x : Float) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem predict_exact_points 
  {points : List Point}
  {x0 y0 : Float}
  (h_len : points.length = 5) 
  (h_unique : ∀ i j, i < j → i < points.length → j < points.length → 
    (points.get ⟨i, by sorry⟩).1 ≠ (points.get ⟨j, by sorry⟩).1) 
  (h_bounds : ∀ p ∈ points, -5 ≤ p.1 ∧ p.1 ≤ 5 ∧ -5 ≤ p.2 ∧ p.2 ≤ 5)
  (h_spacing : ∀ i, i < points.length - 1 → 
    (points.get ⟨i+1, by sorry⟩).1 - (points.get ⟨i, by sorry⟩).1 > 0.1)
  (h_point : (x0, y0) = points.get ⟨2, by sorry⟩) :
  let m : Datamining := {points := points}
  abs (predict m x0 - y0) < 0.000001 := sorry
-- </vc-theorems>