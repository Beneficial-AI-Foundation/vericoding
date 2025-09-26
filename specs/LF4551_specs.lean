-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Vector.add : Vector → Vector → Vector
  | v1, v2 => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vector_addition_coordinates (v1 v2 : Vector) :
  let result := v1.add v2
  result.x = v1.x + v2.x ∧ result.y = v1.y + v2.y :=
sorry

theorem vector_addition_commutative (v1 v2 : Vector) : 
  v1.add v2 = v2.add v1 :=
sorry

theorem zero_vector_identity (v : Vector) :
  let zero := Vector.mk 0 0
  v.add zero = v :=
sorry

theorem inverse_vector_sum_zero (v : Vector) :
  let inverse := Vector.mk (-v.x) (-v.y)
  let result := v.add inverse
  result.x = 0 ∧ result.y = 0 :=
sorry
-- </vc-theorems>