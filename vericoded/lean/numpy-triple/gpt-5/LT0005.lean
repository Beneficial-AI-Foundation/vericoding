import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem vector_get_rfl {α} {n : Nat} (v : Vector α n) (i : Fin n) : v.get i = v.get i := rfl
-- </vc-helpers>

-- <vc-definitions>
def asmatrix {n : Nat} (data : Vector Float n) : Id (Vector Float n) :=
  data
-- </vc-definitions>

-- <vc-theorems>
theorem asmatrix_spec {n : Nat} (data : Vector Float n) :
    ⦃⌜True⌝⦄
    asmatrix data
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = data.get i⌝⦄ := by
  intro _; intro i; rfl
-- </vc-theorems>
