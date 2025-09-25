-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mgrid {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mgrid_spec {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) 
    (h_step_pos : step > 0) (h_range : start < stop) :
    ⦃⌜step > 0 ∧ start < stop ∧ n = ((stop - start) / step).toUInt64.toNat⌝⦄
    mgrid start stop step h_valid
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = start + Float.ofNat i.val * step ∧
                 result.get i < stop⌝⦄ := by
  sorry
-- </vc-theorems>