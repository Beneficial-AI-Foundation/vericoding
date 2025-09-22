-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Represents the result of expanding dimensions of a vector.
    For axis=0, we get a 1×n matrix (row vector).
    For axis=1, we get an n×1 matrix (column vector). -/
inductive ExpandedVector (T : Type) (n : Nat) where
  | rowVector : Vector T n → ExpandedVector T n      -- axis=0: shape (1, n)
  | columnVector : Vector T n → ExpandedVector T n   -- axis=1: shape (n, 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def expand_dims {n : Nat} (a : Vector T n) (axis : Nat) : Id (ExpandedVector T n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expand_dims_spec {n : Nat} (a : Vector T n) (axis : Nat) (h_axis : axis ≤ 1) :
    ⦃⌜axis ≤ 1⌝⦄
    expand_dims a axis
    ⦃⇓result => ⌜match result with
                | ExpandedVector.rowVector v => axis = 0 ∧ v = a
                | ExpandedVector.columnVector v => axis = 1 ∧ v = a⌝⦄ := by
  sorry
-- </vc-theorems>