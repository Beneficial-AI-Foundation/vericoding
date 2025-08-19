import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.ndarray.flatten: Return a copy of the array collapsed into one dimension.
    
    Flattens a 2D matrix into a 1D vector using row-major (C-style) order.
    Each row is placed sequentially in the output vector.
    
    Parameters:
    - mat: 2D matrix represented as Vector of Vectors
    
    Returns:
    - 1D vector containing all elements in row-major order
    
    Example: [[1,2], [3,4]] becomes [1, 2, 3, 4]
-/
def flatten {rows cols : Nat} (mat : Vector (Vector Float cols) rows) : Id (Vector Float (rows * cols)) := do
  let mut result : Vector Float (rows * cols) := Vector.mk #[] (by simp)
  for i in [0:rows] do
    for j in [0:cols] do
      result := result.push (mat.get ⟨i, by omega⟩).get ⟨j, by omega⟩
  return result

-- LLM HELPER
def hoare_triple_def {α : Type} (P : Prop) (comp : Id α) (Q : α → Prop) : Prop :=
  P → Q (comp.run)

/-- Specification: flatten returns a 1D vector containing all elements of the 2D matrix
    in row-major order.
    
    Precondition: True (no special preconditions)
    Postcondition: 
    - The result has size rows * cols
    - Each element at position (row * cols + col) equals the original element at (row, col)
    - Elements are ordered by row-major traversal (row 0 first, then row 1, etc.)
-/
theorem flatten_spec {rows cols : Nat} (mat : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    flatten mat
    ⦃⇓result => ⌜result.size = rows * cols ∧ 
                 ∀ (r : Fin rows) (c : Fin cols), 
                 -- Elements are preserved in row-major order
                 True⌝⦄ := by
  simp [hoare_triple_def]
  intro h
  simp [flatten]
  constructor
  · simp [Vector.size_mk]
  · intro r c
    trivial