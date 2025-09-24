-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def empty (n : Nat) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_spec (n : Nat) :
    ⦃⌜True⌝⦄
    empty n
    ⦃⇓result => ⌜∀ i : Fin n, ∃ v : Float, result.get i = v⌝⦄ := by
  sorry
-- </vc-theorems>