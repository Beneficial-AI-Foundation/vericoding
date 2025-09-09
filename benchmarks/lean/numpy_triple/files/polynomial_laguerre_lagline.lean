import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def lagline (off scl : Float) : Id (Vector Float 2) :=
  sorry

theorem lagline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    lagline off scl
    ⦃⇓result => ⌜(scl = 0 → result.get 0 = off ∧ result.get 1 = 0) ∧
                 (scl ≠ 0 → result.get 0 = off + scl ∧ result.get 1 = -scl)⌝⦄ := by
  sorry
