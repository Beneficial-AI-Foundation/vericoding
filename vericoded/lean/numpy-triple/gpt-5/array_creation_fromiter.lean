import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem Vector.get_ofFn' {α : Type _} {n : Nat}
    (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simpa using Vector.get_ofFn f i
-- </vc-helpers>

-- <vc-definitions>
def fromiter {α : Type} (n : Nat) (iter : Fin n → α) : Id (Vector α n) :=
  pure (Vector.ofFn iter)
-- </vc-definitions>

-- <vc-theorems>
theorem fromiter_spec {α : Type} (n : Nat) (iter : Fin n → α) :
    ⦃⌜True⌝⦄
    fromiter n iter
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = iter i⌝⦄ := by
  simpa [fromiter, Vector.get_ofFn'] using
    (by
      intro (_ : True)
      intro (i : Fin n)
      simp [Vector.get_ofFn'])
-- </vc-theorems>
