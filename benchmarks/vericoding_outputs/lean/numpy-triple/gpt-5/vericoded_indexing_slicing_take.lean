import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers required for this file
-- </vc-helpers>

-- <vc-definitions>
def take {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) : Id (Vector Float m) :=
  pure <| Vector.ofFn (fun i => arr.get (indices.get i))
-- </vc-definitions>

-- <vc-theorems>
theorem take_spec {n m : Nat} (arr : Vector Float n) (indices : Vector (Fin n) m) :
    ⦃⌜True⌝⦄
    take arr indices
    ⦃⇓result => ⌜∀ i : Fin m, result.get i = arr.get (indices.get i)⌝⦄ := by
  simpa [take] using
    (by
      intro i
      simp)
-- </vc-theorems>
