-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allclose {n : Nat} (a b : Vector Float n) (rtol atol : Float) : Id Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem allclose_spec {n : Nat} (a b : Vector Float n) (rtol atol : Float) 
    (h_rtol : rtol >= 0) (h_atol : atol >= 0) :
    ⦃⌜rtol >= 0 ∧ atol >= 0⌝⦄
    allclose a b rtol atol
    ⦃⇓result => ⌜result = (∀ i : Fin n, Float.abs (a.get i - b.get i) <= atol + rtol * Float.abs (b.get i))⌝⦄ := by
  sorry
-- </vc-theorems>