-- <vc-preamble>
def Vector.toTuple (v : Vector) : Int × Int × Int := sorry
def Vector.fromList (l : List Int) : Vector := sorry

def Vector.add (v1 v2 : Vector) : Vector := sorry
def Vector.sub (v1 v2 : Vector) : Vector := sorry

def Vector.dot (v1 v2 : Vector) : Int := sorry
def Vector.cross (v1 v2 : Vector) : Vector := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Vector.magnitude (v : Vector) : Float := sorry
def Vector.toString (v : Vector) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vector_creation_args (x y z : Int) :
  (Vector.toTuple ⟨x, y, z⟩) = (x, y, z) := sorry

theorem vector_creation_list (l : List Int) (h : l.length = 3) :
  Vector.toTuple (Vector.fromList l) = (l[0]!, l[1]!, l[2]!) := sorry

theorem vector_addition (v1 v2 : Vector) :
  Vector.toTuple (Vector.add v1 v2) = (v1.x + v2.x, v1.y + v2.y, v1.z + v2.z) := sorry

theorem vector_subtraction (v1 v2 : Vector) :
  Vector.toTuple (Vector.sub v1 v2) = (v1.x - v2.x, v1.y - v2.y, v1.z - v2.z) := sorry

theorem vector_dot_product (v1 v2 : Vector) :
  Vector.dot v1 v2 = v1.x * v2.x + v1.y * v2.y + v1.z * v2.z := sorry

theorem vector_cross_product (v1 v2 : Vector) :
  Vector.toTuple (Vector.cross v1 v2) = 
    (v1.y * v2.z - v1.z * v2.y,
     v1.z * v2.x - v1.x * v2.z,
     v1.x * v2.y - v1.y * v2.x) := sorry

theorem vector_magnitude (v : Vector) :
  Vector.magnitude v = Float.sqrt (Float.ofInt (v.x * v.x + v.y * v.y + v.z * v.z)) := sorry

theorem vector_string_representation (v : Vector) :
  Vector.toString v = s!"<{v.x}, {v.y}, {v.z}>" := sorry
-- </vc-theorems>