/-
# NumPy Reshape Specification

Port of np_reshape.dfy to Lean 4
-/

namespace DafnySpecs.NpReshape

-- LLM HELPER
def Vector (α : Type*) (n : Nat) : Type* := { l : List α // l.length = n }

-- LLM HELPER
def Vector.ofFn {α : Type*} {n : Nat} (f : Nat → α) : Vector α n :=
  ⟨List.ofFn f, List.length_ofFn f⟩

-- LLM HELPER
def Vector.getElem {α : Type*} {n : Nat} (v : Vector α n) (i : Nat) : α :=
  v.val.get! i

-- LLM HELPER
instance {α : Type*} {n : Nat} : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem v i _ := v.val.get! i

-- LLM HELPER
def Vector.toList {α : Type*} {n : Nat} (v : Vector α n) : List α := v.val

-- LLM HELPER
def Matrix (m k : Nat) (α : Type*) : Type* := Vector (Vector α k) m

-- LLM HELPER
def Matrix.toList {α : Type*} {m k : Nat} (mat : Matrix m k α) : List (Vector α k) := mat.toList

/-- Reshape vector to new dimensions -/
def reshape {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2) : Matrix m k Int := 
  Vector.ofFn (fun i => Vector.ofFn (fun j => a[i * k + j]!))

-- LLM HELPER
lemma vector_toList_length {α : Type*} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  exact v.property

-- LLM HELPER
lemma matrix_toList_length {α : Type*} {m k : Nat} (mat : Matrix m k α) : mat.toList.length = m := by
  exact mat.property

-- LLM HELPER
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Nat → α) (i : Nat) (h : i < n) : 
  (Vector.ofFn f)[i]! = f i := by
  simp [Vector.getElem, Vector.ofFn]
  rw [List.get!_ofFn]

/-- Specification: Element count is preserved -/
theorem reshape_count {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ret.toList.length = n := by
  simp [reshape]
  rw [matrix_toList_length]
  rw [← h2]
  rfl

/-- Specification: Elements are correctly mapped -/
theorem reshape_spec {n m k : Nat} (a : Vector Int n) (newshape : Vector Int 2)
  (h1 : newshape[0]! = m ∧ newshape[1]! = k)
  (h2 : n = m * k) :
  let ret := reshape a newshape
  ∀ i j : Nat, i < m → j < k → ret[i]![j]! = a[i * k + j]! := by
  intro i j hi hj
  simp [reshape, Vector.getElem, Vector.ofFn]
  rw [List.get!_ofFn, List.get!_ofFn]

end DafnySpecs.NpReshape