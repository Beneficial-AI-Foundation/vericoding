import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma vector_get_ofFn_const_one {n : Nat} {T : Type} [OfNat T 1] (i : Fin n) :
    (Vector.ofFn (fun _ => (1 : T))).get i = (1 : T) := by
  simpa [Vector.get_ofFn]
-- </vc-helpers>

-- <vc-definitions>
def ones_like {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) : Id (Vector T n) :=
  return Vector.ofFn (fun _ => (1 : T))
-- </vc-definitions>

-- <vc-theorems>
theorem ones_like_spec {n : Nat} {T : Type} [OfNat T 1] (a : Vector T n) :
    ⦃⌜True⌝⦄
    ones_like a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 1⌝⦄ := by
  simpa [ones_like] using
  (by
    intro (_ : True)
    intro i
    simp)
-- </vc-theorems>
