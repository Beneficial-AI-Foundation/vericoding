import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def vecdot {n : Nat} (x1 x2 : Vector Float n) : Id Float :=
  sorry

theorem vecdot_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    vecdot x1 x2
    ⦃⇓result => ⌜result = List.sum (List.zipWith (· * ·) x1.toList x2.toList) ∧
                 result = List.sum (List.zipWith (· * ·) x2.toList x1.toList)⌝⦄ := by
  sorry
