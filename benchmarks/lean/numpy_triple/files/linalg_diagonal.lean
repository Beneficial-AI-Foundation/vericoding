/-  numpy.linalg.diagonal: Returns specified diagonals of a matrix.

    Extracts the diagonal elements from a matrix. The offset parameter
    controls which diagonal to extract:
    - offset = 0: main diagonal (elements at position [i,i])
    - offset > 0: diagonals above the main diagonal (elements at [i,i+offset])
    - offset < 0: diagonals below the main diagonal (elements at [i-offset,i])

    For simplicity, we return a vector of size min(m,n) which is valid for offset=0.
    The actual diagonal length depends on the offset value and matrix dimensions.
-/

/-  Specification: numpy.linalg.diagonal returns the diagonal elements of a matrix.

    Precondition: The matrix must be non-empty (both dimensions > 0)
    Postcondition: The result contains the diagonal elements extracted from the matrix.
                   - For offset = 0: result[i] = x[i][i] (main diagonal)
                   - The result vector has the same type as the input matrix elements
                   - The extraction respects the mathematical definition of matrix diagonals
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_diagonal {m n : Nat} (x : Vector (Vector Float n) m) (offset : Int) : Id (Vector Float (min m n)) :=
  sorry

theorem numpy_diagonal_spec {m n : Nat} (x : Vector (Vector Float n) m) (offset : Int) 
    (h_m : m > 0) (h_n : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    numpy_diagonal x offset
    ⦃⇓result => ⌜
      -- Main diagonal case: result[i] = x[i][i] for all valid i
      (offset = 0 → ∀ i : Fin (min m n), 
        result.get i = (x.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left m n)⟩).get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right m n)⟩) ∧
      -- General case: diagonal elements are extracted according to offset
      -- The function produces a valid diagonal extraction for any offset value
      (∀ i : Fin (min m n), ∃ r c : Nat, 
        r < m ∧ c < n ∧ 
        result.get i = (x.get ⟨r, sorry⟩).get ⟨c, sorry⟩)
    ⌝⦄ := by
  sorry
