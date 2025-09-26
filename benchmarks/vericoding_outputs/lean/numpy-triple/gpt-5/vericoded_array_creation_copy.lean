import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def copy {n : Nat} (a : Vector α n) : Id (Vector α n) :=
  pure a
-- </vc-definitions>

-- <vc-theorems>
theorem copy_spec {n : Nat} (a : Vector α n) :
    ⦃⌜True⌝⦄
    copy a
    ⦃⇓result => ⌜∀ i : Fin n, result[i] = a[i]⌝⦄ := by
  simpa [copy] using (by
  intro (_h : True)
  exact fun i => rfl)
-- </vc-theorems>
