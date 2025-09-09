import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def chebline (off scl : Float) : Id (Vector Float 2) :=
  sorry

theorem chebline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    chebline off scl
    ⦃⇓result => ⌜result.get ⟨0, by decide⟩ = off ∧ 
                 result.get ⟨1, by decide⟩ = scl⌝⦄ := by
  sorry
