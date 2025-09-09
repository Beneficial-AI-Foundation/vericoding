import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def legline (off scl : Float) : Id (Vector Float 2) :=
  sorry

theorem legline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    legline off scl
    ⦃⇓result => 
      ⌜result.get 0 = off ∧ 
       result.get 1 = scl⌝⦄ := by
  sorry
