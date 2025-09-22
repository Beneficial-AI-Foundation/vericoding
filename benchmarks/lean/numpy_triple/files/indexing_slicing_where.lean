-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def «where» {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem where_spec {n : Nat} (condition : Vector Bool n) (x y : Vector Float n) :
    ⦃⌜True⌝⦄
    «where» condition x y
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = if condition.get i then x.get i else y.get i⌝⦄ := by
  sorry
-- </vc-theorems>