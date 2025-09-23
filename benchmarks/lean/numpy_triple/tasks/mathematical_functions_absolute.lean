-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def absolute {n : Nat} (x : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem absolute_spec {n : Nat} (x : Vector Int n) :
    ⦃⌜True⌝⦄
    absolute x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = if x.get i ≥ 0 then x.get i else -x.get i) ∧
                 (∀ i : Fin n, result.get i ≥ 0) ∧
                 (∀ i : Fin n, result.get i = 0 ↔ x.get i = 0) ∧
                 (∀ i : Fin n, ∀ (y : Int), 
                    (if (x.get i * y) ≥ 0 then (x.get i * y) else -(x.get i * y)) = 
                    result.get i * (if y ≥ 0 then y else -y))⌝⦄ := by
  sorry
-- </vc-theorems>