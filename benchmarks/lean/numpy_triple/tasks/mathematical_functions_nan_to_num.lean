-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Batteries.Lean.Float
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nan_to_num {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nan_to_num_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    nan_to_num x
    ⦃⇓result => ⌜(∀ i : Fin n, 
      let xi := x.get i
      let ri := result.get i
      (xi.isNaN → ri = 0.0) ∧
      (xi = Float.inf → ri > 0 ∧ ri.isFinite) ∧
      (xi = -Float.inf → ri < 0 ∧ ri.isFinite) ∧
      (xi.isFinite → ri = xi)) ∧
    (∀ i : Fin n, (result.get i).isFinite)⌝⦄ := by
  sorry
-- </vc-theorems>