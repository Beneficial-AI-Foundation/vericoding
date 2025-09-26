import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic lemmas for Vector operations
lemma Vector.get_ofFn_eq {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get_ofFn]
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
  unfold fromiter
  -- For Id monad, the Hoare triple reduces to direct property verification
  intro _
  intro i
  exact Vector.get_ofFn_eq iter i
-- </vc-theorems>
