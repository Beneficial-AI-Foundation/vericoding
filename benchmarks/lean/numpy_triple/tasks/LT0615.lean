-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isalnum {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isalnum_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isalnum a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (a.get i ≠ "" ∧ (a.get i).all Char.isAlphanum)⌝⦄ := by
  sorry
-- </vc-theorems>