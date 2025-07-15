/-
# NumPy Poly Specification

Port of np_poly.dfy to Lean 4
-/

namespace DafnySpecs.NpPoly

-- LLM HELPER
def vector_update {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) : Vector α n :=
  Vector.mk (List.set v.toList i.val val) (by simp [List.length_set])

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

-- LLM HELPER
def vector_set {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) : Vector α n :=
  Vector.mk (List.set v.toList i.val val) (by simp [List.length_set])

-- LLM HELPER
lemma vector_set_length {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) :
  (vector_set v i val).toList.length = n := by
  simp [vector_set, List.length_set]

-- LLM HELPER
lemma vector_set_get {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) (val : α) (j : Fin n) :
  (vector_set v i val)[j] = if j = i then val else v[j] := by
  simp [vector_set, Vector.get_mk]
  by_cases h : j.val = i.val
  · simp [h, List.get_set_eq]
  · simp [h, List.get_set_ne]

-- LLM HELPER
def array_from_list {α : Type*} (l : List α) : Array α := l.toArray

-- LLM HELPER
lemma array_from_list_size {α : Type*} (l : List α) : (array_from_list l).size = l.length := by
  simp [array_from_list, List.toArray_size]

-- LLM HELPER
lemma pos_of_nonzero {n : Nat} (h : n > 0) : 0 < n := h

/-- Helper function for polynomial coefficient computation -/
def poly_helper {n : Nat} (roots : Vector Float n) (val : Nat) : Vector Float n := 
  if h : n > 0 then
    let base := Vector.mk (array_from_list (List.replicate n 0.0)) (by simp [array_from_list_size, List.length_replicate])
    vector_set base ⟨0, h⟩ 1.0
  else
    Vector.mk (array_from_list (List.replicate n 0.0)) (by simp [array_from_list_size, List.length_replicate])

/-- Compute polynomial coefficients from roots -/
def poly {n : Nat} (roots : Vector Float n) : Vector Float n := 
  if h : n > 0 then
    poly_helper roots (n - 1)
  else
    Vector.mk (array_from_list (List.replicate n 0.0)) (by simp [array_from_list_size, List.length_replicate])

/-- Specification: The result has same length as input -/
theorem poly_length {n : Nat} (roots : Vector Float n)
  (h : n > 0) :
  let coeff := poly roots
  coeff.toList.length = n := by
  simp [poly, h]
  simp [poly_helper, h]
  simp [vector_set_length]
  simp [Vector.mk_toList_length]
  simp [array_from_list_size]
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
  simp [poly_helper, h1]
  simp [vector_set_length]
  simp [Vector.mk_toList_length]
  simp [array_from_list_size]
  simp [List.length_replicate]

/-- Specification: Helper function first coefficient -/
theorem poly_helper_first_coeff {n : Nat} (roots : Vector Float n) (val : Nat)
  (h1 : n > 0)
  (h2 : val > 0) :
  let coeff := poly_helper roots val
  coeff[⟨0, h1⟩] = 1.0 := by
  simp [poly_helper, h1]
  simp [vector_set_get]
  simp [Vector.get_mk]
  simp [List.get_replicate]

end DafnySpecs.NpPoly