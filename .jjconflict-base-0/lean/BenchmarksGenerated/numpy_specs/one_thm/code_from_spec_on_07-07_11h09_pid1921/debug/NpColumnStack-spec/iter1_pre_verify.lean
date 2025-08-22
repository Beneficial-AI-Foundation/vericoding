namespace NpColumnStack

def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix Int m n := 
  Matrix.of (fun i j => input[j]![i]!)

theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  (ret.toList.length = m * n) ∧
  (∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[j]![i]! = input[i]![j]!) := by
  constructor
  · -- LLM HELPER
    have h_matrix_length : ret.toList.length = m * n := by
      simp [column_stack, Matrix.toList_length]
    exact h_matrix_length
  · -- LLM HELPER
    intros i j hi hj
    simp [column_stack, Matrix.of_apply]
    rfl

end NpColumnStack