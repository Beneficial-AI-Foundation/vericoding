import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper code needed
-- </vc-helpers>

-- <vc-definitions>
def asanyarray {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  pure a
-- </vc-definitions>

-- <vc-theorems>
theorem asanyarray_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    asanyarray a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = a.get i⌝⦄ := by
  simpa [asanyarray] using (by
  intro (_h : True)
  intro (i : Fin n)
  rfl
)
-- </vc-theorems>
