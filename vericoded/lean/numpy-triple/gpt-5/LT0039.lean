import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def atleast_1d {n : Nat} (arr : Vector Float n) : Id (Vector Float n) :=
  pure arr
-- </vc-definitions>

-- <vc-theorems>
theorem atleast_1d_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    atleast_1d arr
    ⦃⇓result => ⌜result = arr ∧ (∀ i : Fin n, result.get i = arr.get i)⌝⦄ := by
  simpa [atleast_1d] using
    (by
      intro (_h : True)
      refine And.intro rfl ?_
      intro i
      rfl)
-- </vc-theorems>
