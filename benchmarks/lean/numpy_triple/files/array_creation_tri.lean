-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tri (N M : Nat) (k : Int) : Id (Vector (Vector Float M) N) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tri_spec (N M : Nat) (k : Int) :
    ⦃⌜True⌝⦄
    tri N M k
    ⦃⇓result => ⌜∀ (i : Fin N) (j : Fin M), 
                  (result.get i).get j = if (j.val : Int) ≤ (i.val : Int) + k then 1.0 else 0.0⌝⦄ := by
  sorry
-- </vc-theorems>