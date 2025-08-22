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
  (mat.get i).get j

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  List.join (mat.toList.map (fun row => row.toList))

/-- Stack vectors as columns to form a matrix -/
def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix Int m n := 
  Matrix.of fun i j => (input.get j).get i

/-- Specification: The result has correct dimensions -/
theorem column_stack_dimensions {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ret.toList.length = m * n := by
  unfold column_stack Matrix.toList
  simp only [Vector.toList_ofFn, List.map_map, List.join_map_map]
  rw [List.length_join, List.map_map]
  simp only [Vector.toList_ofFn, List.length_map, List.length_range]
  rw [List.sum_const, List.length_range]
  simp

/-- Specification: Elements are correctly placed -/
theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ∀ (i : Nat) (j : Nat) (hi : i < n) (hj : j < m), Matrix.get ret ⟨j, hj⟩ ⟨i, hi⟩ = (input.get ⟨i, hi⟩).get ⟨j, hj⟩ := by
  intros i j hi hj
  unfold column_stack Matrix.get Matrix.of
  simp only [Vector.get_ofFn]

end DafnySpecs.NpColumnStack