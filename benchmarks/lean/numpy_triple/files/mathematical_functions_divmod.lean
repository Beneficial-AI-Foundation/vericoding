-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divmod {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n × Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divmod_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    divmod x1 x2
    ⦃⇓result => ⌜let (quotient, remainder) := result
                  ∀ i : Fin n, 
                    quotient.get i = (x1.get i / x2.get i).floor ∧
                    remainder.get i = x1.get i - x2.get i * quotient.get i ∧
                    x1.get i = x2.get i * quotient.get i + remainder.get i ∧
                    (x2.get i > 0 → 0 ≤ remainder.get i ∧ remainder.get i < x2.get i) ∧
                    (x2.get i < 0 → x2.get i < remainder.get i ∧ remainder.get i ≤ 0)⌝⦄ := by
  sorry
-- </vc-theorems>