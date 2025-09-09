import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def tan {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem tan_spec {n : Nat} (x : Vector Float n) 
    (h_valid : ∀ i : Fin n, Float.cos (x.get i) ≠ 0) :
    ⦃⌜∀ i : Fin n, Float.cos (x.get i) ≠ 0⌝⦄
    tan x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.tan (x.get i) ∧ 
                                result.get i = Float.sin (x.get i) / Float.cos (x.get i)⌝⦄ := by
  sorry
