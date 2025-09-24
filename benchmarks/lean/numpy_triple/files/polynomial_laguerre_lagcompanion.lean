-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lagcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lagcompanion_spec {n : Nat} (c : Vector Float (n + 2)) 
    (h_nonzero : c.get (Fin.last (n + 1)) ≠ 0) :
    ⦃⌜c.get (Fin.last (n + 1)) ≠ 0⌝⦄
    lagcompanion c
    ⦃⇓mat => ⌜-- Matrix has correct dimensions
             mat.size = n + 1 ∧ 
             (∀ i : Fin (n + 1), (mat.get i).size = n + 1) ∧
             -- Diagonal elements follow pattern: 2*i + 1  
             (∀ i : Fin (n + 1), (mat.get i).get i = 2 * Float.ofNat i.val + 1) ∧
             -- Off-diagonal elements for tridiagonal structure
             (∀ i : Fin n, (mat.get (i.castSucc)).get (i.succ) = -(Float.ofNat i.val + 1)) ∧
             (∀ i : Fin n, (mat.get (i.succ)).get (i.castSucc) = -(Float.ofNat i.val + 1))⌝⦄ := by
  sorry
-- </vc-theorems>