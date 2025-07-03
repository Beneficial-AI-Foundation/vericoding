/-
# NumPy Abs Specification

Port of np_abs.dfy to Lean 4
-/

namespace DafnySpecs.NpAbs

/-- Absolute value of an integer -/
def absInt (x : Int) : Int := if x < 0 then -x else x

/-- Element-wise absolute value of a vector -/
def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map absInt a

/-- Specification: The result has the same length as input -/
theorem abs_length {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n := by
  simp [abs, Vector.toList_map]

/-- Specification: Each element is the absolute value of the corresponding input element -/
theorem abs_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] = absInt (a[i]) := by
  intro i
  simp [abs]
  rw [Vector.get_map]

/-- Specification: All elements in the result are non-negative -/
theorem abs_nonnegative {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] ≥ 0 := by
  intro i
  rw [abs_spec]
  unfold absInt
  by_cases h : a[i] < 0
  · simp [h]
    exact neg_nonneg_of_nonpos (le_of_lt h)
  · simp [h]
    exact le_of_not_gt h

end DafnySpecs.NpAbs