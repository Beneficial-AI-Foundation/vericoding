-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isdigit {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isdigit_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isdigit a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (a.get i ≠ "" ∧ (a.get i).all Char.isDigit)⌝⦄ := by
  sorry
-- </vc-theorems>