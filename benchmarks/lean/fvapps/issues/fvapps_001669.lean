-- <vc-preamble>
def Points := List Point

structure Triangle where
  points : List Point
  valid : points.length = 3

structure Result where
  numTriangles : Option Int
  area : Option Float  
  triangles : Option (List Triangle)

def biggest_triang_int (points : Points) (center : Point) (radius : Int) : Result :=
  sorry

def norme (p : Point) : Float :=
  sorry

def vectorize (p1 p2 : Point) : Point := 
  sorry

def isInCircle (p : Point) (center : Point) (radius : Int) : Bool :=
  sorry

def crossProd (v1 v2 : Point) : Point :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def origin : Point := {
  coords := [0,0,0]
  valid := by simp
}
-- </vc-definitions>

-- <vc-theorems>
theorem output_structure 
  (points : Points) 
  (center : Point) 
  (radius : Int)
  (h1 : points.length ≥ 3)
  (h4 : radius > 0) :
  let result := biggest_triang_int points center radius
  (result.numTriangles.isSome → 
   result.area.isSome ∧
   result.triangles.isSome) :=
sorry

theorem empty_small_inputs
  (points : Points)
  (h1 : points.length < 3) :
  let result := biggest_triang_int points origin 10
  result.numTriangles = none ∧
  result.area = none ∧
  result.triangles = none :=
sorry
-- </vc-theorems>