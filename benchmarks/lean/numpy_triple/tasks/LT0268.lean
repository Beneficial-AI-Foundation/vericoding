-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isnan {n : Nat} (x : Vector Float n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isnan_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    isnan x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = (x.get i).isNaN) ∧
                 (∀ i : Fin n, result.get i = true → ¬(x.get i = x.get i)) ∧
                 (∀ i : Fin n, ¬(x.get i).isNaN → result.get i = false) ∧
                 (∀ i : Fin n, (x.get i).isFinite → result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>