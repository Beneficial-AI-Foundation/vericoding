-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermline (off scl : Float) : Id (Vector Float 2) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    hermline off scl
    ⦃⇓result => ⌜
      result.get ⟨0, by decide⟩ = off ∧
      result.get ⟨1, by decide⟩ = scl / 2
    ⌝⦄ := by
  sorry
-- </vc-theorems>