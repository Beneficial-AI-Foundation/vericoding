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

/-- LLM HELPER -/
lemma Vector.get_map_helper {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v)[i] = f (v[i]) := by
  simp [Vector.get_eq_getElem, Vector.map_def]

/-- Specification: Each element is the absolute value of the corresponding input element -/
theorem abs_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] = absInt (a[i]) := by
  intro i
  simp [abs]
  rw [Vector.get_map]

/-- LLM HELPER -/
lemma absInt_nonneg (x : Int) : 0 ≤ absInt x := by
  simp [absInt]
  by_cases h : x < 0
  · simp [h]
    linarith
  · simp [h]
    linarith

/-- Specification: All elements in the result are non-negative -/
theorem abs_nonnegative {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] ≥ 0 := by
  intro i
  rw [abs_spec]
  exact absInt_nonneg (a[i])

end DafnySpecs.NpAbs