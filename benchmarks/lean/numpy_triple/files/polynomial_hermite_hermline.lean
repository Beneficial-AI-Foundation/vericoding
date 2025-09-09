import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermline (off scl : Float) : Id (Vector Float 2) :=
  sorry

theorem hermline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    hermline off scl
    ⦃⇓result => ⌜
      result.get ⟨0, by decide⟩ = off ∧
      result.get ⟨1, by decide⟩ = scl / 2
    ⌝⦄ := by
  sorry
