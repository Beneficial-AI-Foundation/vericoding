-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remainder {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remainder_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜∀ i : Fin n, x2.get i ≠ 0⌝⦄
    remainder x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, 
      let r := result.get i
      let a := x1.get i  
      let b := x2.get i
      -- Mathematical definition: a = floor(a/b) * b + r
      a = (a / b).floor * b + r ∧
      -- Result has same sign as divisor (when divisor is non-zero)
      (b > 0 → r ≥ 0 ∧ r < b) ∧
      (b < 0 → r ≤ 0 ∧ r > b) ∧
      -- Magnitude bound
      Float.abs r < Float.abs b⌝⦄ := by
  sorry
-- </vc-theorems>