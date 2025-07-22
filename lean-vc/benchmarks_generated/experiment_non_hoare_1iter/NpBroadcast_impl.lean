/-
# NumPy Broadcast Specification

Port of np_broadcast.dfy to Lean 4
-/

namespace DafnySpecs.NpBroadcast

-- LLM HELPER
def Vector (α : Type*) (n : Nat) := { l : List α // l.length = n }

-- LLM HELPER
def Matrix (m n : Nat) (α : Type*) := { mat : List (List α) // mat.length = m ∧ ∀ row ∈ mat, row.length = n }

-- LLM HELPER
def Matrix.ofFn {m n : Nat} (f : Fin m → Fin n → α) : Matrix m n α :=
  ⟨List.range m |>.map (fun i => List.range n |>.map (fun j => f ⟨i, by simp⟩ ⟨j, by simp⟩)), by
    constructor
    · simp
    · intro row hrow
      simp at hrow
      obtain ⟨i, _, rfl⟩ := hrow
      simp⟩

-- LLM HELPER
def Vector.get (v : Vector α n) (i : Nat) : α := v.val.get! i

-- LLM HELPER
notation v "[" i "]!" => Vector.get v i

-- LLM HELPER
def Matrix.get (mat : Matrix m n α) (i : Nat) : List α := mat.val.get! i

-- LLM HELPER
notation mat "[" i "]!" => Matrix.get mat i

-- LLM HELPER
def Matrix.toList {m n : Nat} (mat : Matrix m n α) : List α := mat.val.flatten

/-- Broadcast a vector to a 2D shape -/
def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix (shape[0]!) (shape[1]!) Int :=
  Matrix.ofFn fun i j => 
    if shape[0]! = n then a[i.val]! else a[j.val]!

-- LLM HELPER
lemma matrix_toList_length {m n : Nat} (mat : Matrix m n Int) : mat.toList.length = m * n := by
  simp [Matrix.toList]
  have h1 : mat.val.length = m := mat.property.1
  have h2 : ∀ row ∈ mat.val, row.length = n := mat.property.2
  rw [List.length_flatten]
  simp [h1]
  congr 1
  ext row
  simp
  apply h2
  assumption

/-- Specification: The result has the correct dimensions -/
theorem broadcast_length {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  ret.toList.length = shape[0]! * shape[1]! := by
  simp [broadcast]
  apply matrix_toList_length

/-- Specification: Elements are correctly broadcasted -/
theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  ∀ i j : Nat, i < shape[0]! → j < shape[1]! →
    if shape[0]! = n then ret[i]![j]! = a[i]! else ret[i]![j]! = a[j]! := by
  intro i j hi hj
  simp [broadcast]
  simp [Matrix.ofFn, Matrix.get]
  split_ifs with h_eq
  · rfl
  · rfl

end DafnySpecs.NpBroadcast