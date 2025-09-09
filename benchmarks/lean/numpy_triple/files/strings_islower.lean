import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def islower {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry

theorem islower_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    islower a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 
      ((∃ c ∈ (a.get i).toList, c.isAlpha ∧ c.isLower) ∧ 
       (∀ c ∈ (a.get i).toList, c.isAlpha → c.isLower))⌝⦄ := by
  sorry
