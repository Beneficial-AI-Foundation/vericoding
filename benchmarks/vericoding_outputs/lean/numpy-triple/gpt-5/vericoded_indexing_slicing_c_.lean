import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: simplify running Id.pure
@[simp] theorem id_run_pure {α} (x : α) : (pure x : Id α).run = x := rfl
-- </vc-helpers>

-- <vc-definitions>
def c_ {n : Nat} (arr1 arr2 : Vector Float n) : Id (Vector (Vector Float 2) n) :=
  pure <| Vector.ofFn (fun i => #v[arr1.get i, arr2.get i])
-- </vc-definitions>

-- <vc-theorems>
theorem c_spec {n : Nat} (arr1 arr2 : Vector Float n) :
    ⦃⌜True⌝⦄
    c_ arr1 arr2
    ⦃⇓result => ⌜∀ i : Fin n, 
      result.get i = ⟨#[arr1.get i, arr2.get i], by simp⟩⌝⦄ := by
  intro _ i
  simp [c_]
-- </vc-theorems>
