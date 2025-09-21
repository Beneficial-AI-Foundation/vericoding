-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ufunc_call {n : Nat} (op : Float → Float → Float) (a b : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ufunc_call_spec {n : Nat} (op : Float → Float → Float) (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    ufunc_call op a b
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = op (a.get i) (b.get i)⌝⦄ := by
  sorry
-- </vc-theorems>