-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bmat {n : Nat} (topLeft topRight bottomLeft bottomRight : Vector Float n) : Id (Vector Float (4 * n)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bmat_spec {n : Nat} (topLeft topRight bottomLeft bottomRight : Vector Float n) :
    ⦃⌜True⌝⦄
    bmat topLeft topRight bottomLeft bottomRight
    ⦃⇓result => ⌜(∀ i : Fin n, result.get ⟨i.val, by omega⟩ = topLeft.get i) ∧
                 (∀ i : Fin n, result.get ⟨i.val + n, by omega⟩ = topRight.get i) ∧
                 (∀ i : Fin n, result.get ⟨i.val + 2*n, by omega⟩ = bottomLeft.get i) ∧
                 (∀ i : Fin n, result.get ⟨i.val + 3*n, by omega⟩ = bottomRight.get i)⌝⦄ := by
  sorry
-- </vc-theorems>