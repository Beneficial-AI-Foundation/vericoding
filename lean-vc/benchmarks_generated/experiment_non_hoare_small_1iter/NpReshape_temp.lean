/-
# NumPy Reshape Specification

Port of np_reshape.dfy to Lean 4
-/

import benchmarks.MatrixDef

namespace DafnySpecs.NpReshape

/-- Reshape vector to new dimensions -/
def reshape {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2) : Matrix m k Int := 
  Vector.ofFn (fun i => Vector.ofFn (fun j => a[i * k + j]!))

-- LLM HELPER
lemma vector_toList_length {α : Type*} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  simp [Vector.toList]

-- LLM HELPER
lemma matrix_toList_length {α : Type*} {m k : Nat} (mat : Matrix m k α) : mat.toList.length = m := by
  simp [Matrix.toList, Vector.toList]

-- LLM HELPER
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Nat → α) (i : Nat) (h : i < n) : 
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

/-- Specification: Element count is preserved -/
theorem reshape_count {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ret.toList.length = n := by
  simp [reshape]
  rw [matrix_toList_length]
  rw [h1.1, h2]

/-- Specification: Elements are correctly mapped -/
theorem reshape_spec {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ∀ i j : Nat, i < m → j < k → ret[i]![j]! = a[i * k + j]! := by
  intro i j hi hj
  simp [reshape]
  simp [Vector.ofFn, Vector.get]

end DafnySpecs.NpReshape