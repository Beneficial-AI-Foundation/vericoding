-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def outer {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) : Id (Vector (Vector α n) m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem outer_spec {m n : Nat} [Mul α] (a : Vector α m) (b : Vector α n) :
    ⦃⌜True⌝⦄
    outer a b
    ⦃⇓result => ⌜
      -- Core property: Each matrix element is the product of corresponding vector elements
      -- This captures the fundamental definition of outer product: (a ⊗ b)[i,j] = a[i] * b[j]
      ∀ (i : Fin m) (j : Fin n), (result.get i).get j = a.get i * b.get j
    ⌝⦄ := by
  sorry
-- </vc-theorems>