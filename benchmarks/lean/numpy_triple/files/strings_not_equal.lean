import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def not_equal {n : Nat} (x1 x2 : Vector String n) : Id (Vector Bool n) :=
  sorry

theorem not_equal_spec {n : Nat} (x1 x2 : Vector String n) :
    ⦃⌜True⌝⦄
    not_equal x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (x1.get i ≠ x2.get i)⌝⦄ := by
  sorry
