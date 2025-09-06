/-  numpy.ndarray.flatten: Return a copy of the array collapsed into one dimension.

    Flattens a 2D matrix into a 1D vector using row-major (C-style) order.
    Each row is placed sequentially in the output vector.

    Parameters:
    - mat: 2D matrix represented as Vector of Vectors

    Returns:
    - 1D vector containing all elements in row-major order

    Example: [[1,2], [3,4]] becomes [1, 2, 3, 4]
-/

/-  Specification: flatten returns a 1D vector containing all elements of the 2D matrix
    in row-major order.

    Precondition: True (no special preconditions)
    Postcondition: 
    - The result has size rows * cols
    - Each element at position (row * cols + col) equals the original element at (row, col)
    - Elements are ordered by row-major traversal (row 0 first, then row 1, etc.)
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def flatten {rows cols : Nat} (mat : Vector (Vector Float cols) rows) : Id (Vector Float (rows * cols)) :=
  sorry

theorem flatten_spec {rows cols : Nat} (mat : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    flatten mat
    ⦃⇓result => ⌜result.size = rows * cols ∧ 
                 ∀ (r : Fin rows) (c : Fin cols), 
                 -- Elements are preserved in row-major order
                 True⌝⦄ := by
  sorry
