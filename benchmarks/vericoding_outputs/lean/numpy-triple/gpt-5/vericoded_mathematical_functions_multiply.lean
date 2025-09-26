import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def multiply {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  pure <| Vector.ofFn (fun i => x1.get i * x2.get i)
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    multiply x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i * x2.get i⌝⦄ := by
  intro _ i
  simp [multiply]
-- </vc-theorems>
