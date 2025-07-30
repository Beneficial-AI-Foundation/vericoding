/-
# NumPy Transpose Specification

Port of np_transpose.dfy to Lean 4
-/

namespace DafnySpecs.NpTranspose

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := Array (Array α)

-- LLM HELPER
def Matrix.toList {α : Type} {m n : Nat} (mat : Matrix α m n) : List α :=
  mat.toList.flatMap (·.toList)

-- LLM HELPER
def Matrix.get {α : Type} {m n : Nat} (mat : Matrix α m n) (i : Nat) (j : Nat) : α :=
  mat[i]![j]!

/-- Transpose a 2D matrix -/
def transpose {m n : Nat} (a : Matrix Int m n) : Matrix Int n m := 
  Array.ofFn (fun j : Fin n => Array.ofFn (fun i : Fin m => Matrix.get a i.val j.val))

-- LLM HELPER
theorem Array.toList_ofFn_length {α : Type} {n : Nat} (f : Fin n → α) :
  (Array.ofFn f).toList.length = n := by
  simp [Array.toList_ofFn]

-- LLM HELPER
theorem List.sum_replicate {n k : Nat} : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih => 
    simp [List.replicate_succ, ih]
    ring

-- LLM HELPER
theorem List.sum_map_const {α : Type} (l : List α) (k : Nat) : (l.map (fun _ => k)).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => 
    simp [List.map_cons, List.sum_cons, ih]
    ring

/-- Specification: Transpose preserves dimensions -/
theorem transpose_dimensions {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ret.toList.length = n * m := by
  simp [transpose, Matrix.toList, Array.toList_ofFn]
  simp [List.length_flatMap]
  rw [List.sum_map_const]
  simp [Array.toList_ofFn_length]

/-- Specification: Elements are correctly transposed -/
theorem transpose_spec {m n : Nat} (a : Matrix Int m n) :
  let ret := transpose a
  ∀ i j : Nat, i < m → j < n → Matrix.get ret j i = Matrix.get a i j := by
  intro i j hi hj
  simp [transpose, Matrix.get, Array.getElem_ofFn]
  rfl

end DafnySpecs.NpTranspose