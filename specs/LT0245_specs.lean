-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tensordot {n : Nat} (a b : Vector Float n) (axes : Nat) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tensordot_spec {n : Nat} (a b : Vector Float n) (axes : Nat) 
    (h_axes : axes = 1) :
    ⦃⌜axes = 1⌝⦄
    tensordot a b axes
    ⦃⇓result => ⌜result = List.sum (List.zipWith (· * ·) a.toList b.toList)⌝⦄ := by
  sorry
-- </vc-theorems>