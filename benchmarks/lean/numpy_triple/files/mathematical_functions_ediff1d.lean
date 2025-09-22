-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_ediff1d {n : Nat} (ary : Vector Float (n + 1)) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_ediff1d_spec {n : Nat} (ary : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_ediff1d ary
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = ary.get (i.succ) - ary.get (i.castSucc)⌝⦄ := by
  sorry
-- </vc-theorems>