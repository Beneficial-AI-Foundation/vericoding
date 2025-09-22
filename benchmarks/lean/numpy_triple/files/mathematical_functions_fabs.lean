-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fabs {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fabs_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    fabs x
    ⦃⇓result => ⌜∀ i : Fin n, 
                  -- Primary property: result is the absolute value
                  result.get i = Float.abs (x.get i) ∧
                  -- Non-negativity (mathematical property of absolute value)
                  result.get i ≥ 0 ∧
                  -- Idempotence: abs(abs(x)) = abs(x)
                  Float.abs (result.get i) = result.get i ∧
                  -- Symmetry: abs(x) = abs(-x)
                  result.get i = Float.abs (-(x.get i))⌝⦄ := by
  sorry
-- </vc-theorems>