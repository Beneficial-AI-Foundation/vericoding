import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def isdigit {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry

theorem isdigit_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isdigit a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (a.get i ≠ "" ∧ (a.get i).all Char.isDigit)⌝⦄ := by
  sorry
