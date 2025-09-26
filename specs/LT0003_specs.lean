-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def asarray {n : Nat} (a : List Float) (h : a.length = n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem asarray_spec {n : Nat} (a : List Float) (h : a.length = n) :
    ⦃⌜a.length = n⌝⦄
    asarray a h
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a[i.val]'(by rw [h]; exact i.isLt)⌝⦄ := by
  sorry
-- </vc-theorems>