-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermweight {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermweight_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    hermweight x
    ⦃⇓w => ⌜(∀ i : Fin n, w.get i = Float.exp (-(x.get i * x.get i))) ∧
            (∀ i : Fin n, w.get i > 0) ∧
            (∀ i : Fin n, x.get i = 0 → w.get i = 1) ∧
            (∀ i j : Fin n, Float.abs (x.get i) < Float.abs (x.get j) → 
                            w.get i > w.get j)⌝⦄ := by
  sorry
-- </vc-theorems>