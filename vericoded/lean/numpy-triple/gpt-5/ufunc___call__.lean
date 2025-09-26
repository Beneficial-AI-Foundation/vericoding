import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no extra helpers needed
-- </vc-helpers>

-- <vc-definitions>
def ufunc_call {n : Nat} (op : Float → Float → Float) (a b : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => op (a.get i) (b.get i)))
-- </vc-definitions>

-- <vc-theorems>
theorem ufunc_call_spec {n : Nat} (op : Float → Float → Float) (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    ufunc_call op a b
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = op (a.get i) (b.get i)⌝⦄ := by
  simpa [ufunc_call] using (by intro (_ : True); intro i; simp)
-- </vc-theorems>
