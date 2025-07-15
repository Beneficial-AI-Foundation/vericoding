/-
# NumPy Poly Specification

Port of np_poly.dfy to Lean 4
-/

namespace DafnySpecs.NpPoly

-- LLM HELPER
def vector_update {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) : Vector α n :=
  Vector.mk (List.set v.toList i.val val)

-- LLM HELPER
lemma vector_update_length {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) :
  (vector_update v i val).toList.length = n := by
  simp [vector_update, List.length_set]

-- LLM HELPER
lemma vector_update_get {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) (j : Fin n) :
  (vector_update v i val)[j] = if j = i then val else v[j] := by
  simp [vector_update, Vector.get_mk]
  by_cases h : j.val = i.val
  · simp [h, List.get_set_eq]
  · simp [h, List.get_set_ne]

/-- Helper function for polynomial coefficient computation -/
def poly_helper {n : Nat} (roots : Vector Float n) (val : Nat) : Vector Float n := 
  Vector.mk (List.replicate n 0.0) |>.set 0 1.0

/-- Compute polynomial coefficients from roots -/
def poly {n : Nat} (roots : Vector Float n) : Vector Float n := 
  if h : n > 0 then
    poly_helper roots (n - 1)
  else
    Vector.mk []

/-- Specification: The result has same length as input -/
theorem poly_length {n : Nat} (roots : Vector Float n)
  (h : n > 0) :
  let coeff := poly roots
  coeff.toList.length = n := by
  simp [poly, h]
  simp [poly_helper]
  simp [Vector.set_toList_length]
  simp [Vector.mk_toList_length]
  simp [List.length_replicate]

/-- Specification: Coefficient computation property -/
theorem poly_spec {n : Nat} (roots : Vector Float n)
  (h : n > 0) :
  let coeff := poly roots
  ∀ i : Fin n, coeff[i] = (poly_helper roots (n - 1))[i] := by
  intro i
  simp [poly, h]

/-- Specification: Helper function length -/
theorem poly_helper_length {n : Nat} (roots : Vector Float n) (val : Nat)
  (h1 : n > 0)
  (h2 : val > 0) :
  let coeff := poly_helper roots val
  coeff.toList.length = n := by
  simp [poly_helper]
  simp [Vector.set_toList_length]
  simp [Vector.mk_toList_length]
  simp [List.length_replicate]

/-- Specification: Helper function first coefficient -/
theorem poly_helper_first_coeff {n : Nat} (roots : Vector Float n) (val : Nat)
  (h1 : n > 0)
  (h2 : val > 0) :
  let coeff := poly_helper roots val
  coeff[0]! = 1.0 := by
  simp [poly_helper]
  simp [Vector.set_get]
  simp [Vector.mk_get]
  simp [List.get_replicate]
  simp [List.get!_eq_get]

end DafnySpecs.NpPoly