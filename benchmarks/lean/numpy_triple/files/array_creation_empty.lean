import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def empty (n : Nat) : Id (Vector Float n) :=
  sorry

theorem empty_spec (n : Nat) :
    ⦃⌜True⌝⦄
    empty n
    ⦃⇓result => ⌜∀ i : Fin n, ∃ v : Float, result.get i = v⌝⦄ := by
  sorry
