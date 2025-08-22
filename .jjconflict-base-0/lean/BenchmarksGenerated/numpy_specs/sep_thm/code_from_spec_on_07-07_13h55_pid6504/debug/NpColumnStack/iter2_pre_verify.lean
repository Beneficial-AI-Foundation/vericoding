/-
# NumPy Column Stack Specification

Port of np_column_stack.dfy to Lean 4
-/

namespace DafnySpecs.NpColumnStack

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Vector (Vector α n) m

-- LLM HELPER
def Matrix.of {α : Type} {m n : Nat} (f : Fin m → Fin n → α) : Matrix α m n :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => f i j))

-- LLM HELPER
def Matrix.get {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Fin m) (j : Fin n) : α :=
  mat[i]![j]!

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  mat.toList.bind (fun row => row.toList)

/-- Stack vectors as columns to form a matrix -/
def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix Int m n := 
  Matrix.of fun i j => input[j]![i]!

/-- Specification: The result has correct dimensions -/
theorem column_stack_dimensions {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ret.toList.length = m * n := by
  simp [column_stack, Matrix.toList]
  simp [Vector.toList_length]
  ring

/-- Specification: Elements are correctly placed -/
theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[j]![i]! = input[i]![j]! := by
  intros i j hi hj
  simp [column_stack, Matrix.of]
  have hi_fin : i < n := hi
  have hj_fin : j < m := hj
  simp [Vector.get_ofFn]

end DafnySpecs.NpColumnStack