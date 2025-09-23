-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ogrid (start stop step : Float) (n : Nat) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ogrid_spec (start stop step : Float) (n : Nat) 
    (h_step : step ≠ 0) :
    ⦃⌜step ≠ 0⌝⦄
    ogrid start stop step n
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = start + (i.val.toFloat) * step) ∧
                (∀ i : Fin n, 
                  if step > 0 then start ≤ result.get i ∧ result.get i < stop
                  else stop < result.get i ∧ result.get i ≤ start)⌝⦄ := by
  sorry
-- </vc-theorems>