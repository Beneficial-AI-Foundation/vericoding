import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem Vector.get_ofFn_const {α} {n : Nat} (x : α) (i : Fin n) :
    (Vector.ofFn (fun (_ : Fin n) => x)).get i = x := by
  simpa using (Vector.get_ofFn (f := fun (_ : Fin n) => x) (i := i))
-- </vc-helpers>

-- <vc-definitions>
def numpy_full_like {n : Nat} (a : Vector Float n) (fill_value : Float) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun (_ : Fin n) => fill_value))
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_full_like_spec {n : Nat} (a : Vector Float n) (fill_value : Float) :
    ⦃⌜True⌝⦄
    numpy_full_like a fill_value
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = fill_value⌝⦄ := by
  simpa [numpy_full_like] using
    (by
      intro (_ : True)
      intro i
      simp)
-- </vc-theorems>
