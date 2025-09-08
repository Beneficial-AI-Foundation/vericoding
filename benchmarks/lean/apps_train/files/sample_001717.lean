/-
Your task is to build a model^(1) which can predict y-coordinate.
You can pass tests if predicted y-coordinates are inside error margin.

You will receive train set which should be used to build a model. 
After you build a model tests will call function ```predict``` and pass x to it. 

Error is going to be calculated with RMSE.

Side note: Points in test cases are from different polynomials (up to 5th degree).

Easier version: Data mining #1

Blocked libraries: sklearn, pandas, tensorflow, numpy, scipy

Explanation
[1] A mining model is created by applying an algorithm to data, but it is more than an algorithm or a metadata container: it is a set of data, statistics, and patterns that can be applied to new data to generate predictions and make inferences about relationships.
-/

def Point := Float × Float 

structure Datamining where
  points : List Point

-- <vc-helpers>
-- </vc-helpers>

def predict (m : Datamining) (x : Float) : Float := sorry

def abs (x : Float) : Float := sorry

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

-- Apps difficulty: interview
-- Assurance level: guarded