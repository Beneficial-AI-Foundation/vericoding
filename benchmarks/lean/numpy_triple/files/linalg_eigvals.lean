/- 
{
  "name": "numpy.linalg.eigvals",
  "category": "Matrix eigenvalues",
  "description": "Compute the eigenvalues of a general matrix",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.linalg.eigvals.html",
  "doc": "Compute the eigenvalues of a general matrix.\n\nMain difference from eig: Does not compute eigenvectors.\n\nParameters:\n- a: Square array\n\nReturns:\n- w: The eigenvalues, not necessarily ordered",
}
-/

/-  Compute the eigenvalues of a general square matrix -/

/-  Specification: eigvals computes eigenvalues of a square matrix -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Matrix represented as a vector of vectors (rows) -/
def Matrix (n : Nat) (α : Type) : Type := Vector (Vector α n) n
/-- Complex number type for eigenvalues -/
structure Complex where
  re : Float
  im : Float
  deriving Repr

-- <vc-helpers>
-- </vc-helpers>

def eigvals {n : Nat} (a : Matrix (n + 1) Float) : Id (Vector Complex (n + 1)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem eigvals_spec {n : Nat} (a : Matrix (n + 1) Float) :
    ⦃⌜True⌝⦄
    eigvals a
    ⦃⇓w => ⌜-- The result contains exactly n+1 eigenvalues (guaranteed by type)
            -- For diagonal matrices, eigenvalues are the diagonal elements
            -- This captures the key mathematical property from the numpy documentation
            (∀ i j : Fin (n + 1), i ≠ j → (a.get i).get j = 0) →
            (∀ i : Fin (n + 1), ∃ j : Fin (n + 1), (w.get j).re = (a.get i).get i ∧ (w.get j).im = 0)⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
