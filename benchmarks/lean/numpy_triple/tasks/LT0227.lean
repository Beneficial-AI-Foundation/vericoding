-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def eigvals {n : Nat} (a : Matrix (n + 1) Float) : Id (Vector Complex (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem eigvals_spec {n : Nat} (a : Matrix (n + 1) Float) :
    ⦃⌜True⌝⦄
    eigvals a
    ⦃⇓w => ⌜-- The result contains exactly n+1 eigenvalues (guaranteed by type)
            -- For diagonal matrices, eigenvalues are the diagonal elements
            -- This captures the key mathematical property from the numpy documentation
            (∀ i j : Fin (n + 1), i ≠ j → (a.get i).get j = 0) →
            (∀ i : Fin (n + 1), ∃ j : Fin (n + 1), (w.get j).re = (a.get i).get i ∧ (w.get j).im = 0)⌝⦄ := by
  sorry
-- </vc-theorems>