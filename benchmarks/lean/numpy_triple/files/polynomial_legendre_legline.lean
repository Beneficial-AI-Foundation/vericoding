-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legline (off scl : Float) : Id (Vector Float 2) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    legline off scl
    ⦃⇓result => 
      ⌜result.get 0 = off ∧ 
       result.get 1 = scl⌝⦄ := by
  sorry
-- </vc-theorems>