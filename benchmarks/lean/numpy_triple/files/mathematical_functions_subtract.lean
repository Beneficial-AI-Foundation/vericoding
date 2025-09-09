import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def subtract {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem subtract_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    subtract x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i - x2.get i ∧
                  -- Sanity check: subtracting zero preserves the original value
                  (x2.get i = 0 → result.get i = x1.get i) ∧
                  -- Sanity check: subtracting a value from itself yields zero
                  (x1.get i = x2.get i → result.get i = 0) ∧
                  -- Anti-commutativity property can be verified
                  result.get i = -(x2.get i - x1.get i)⌝⦄ := by
  sorry
