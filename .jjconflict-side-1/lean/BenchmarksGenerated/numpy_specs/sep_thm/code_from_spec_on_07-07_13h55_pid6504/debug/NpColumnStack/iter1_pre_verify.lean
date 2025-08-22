/-
# NumPy Column Stack Specification

Port of np_column_stack.dfy to Lean 4
-/

namespace DafnySpecs.NpColumnStack

/-- Stack vectors as columns to form a matrix -/
def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix Int m n := 
  Matrix.of fun i j => input[j]![i]!

/-- Specification: The result has correct dimensions -/
theorem column_stack_dimensions {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ret.toList.length = m * n := by
  simp [column_stack]
  simp [Matrix.toList_length]

/-- Specification: Elements are correctly placed -/
theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].toList.length = m) :
  let ret := column_stack input
  ∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[j]![i]! = input[i]![j]! := by
  intros i j hi hj
  simp [column_stack]
  simp [Matrix.of_apply]

end DafnySpecs.NpColumnStack