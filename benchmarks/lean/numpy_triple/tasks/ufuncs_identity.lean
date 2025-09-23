-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ufunc_identity (op : Float → Float → Float) : Id (Option Float) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ufunc_identity_spec (op : Float → Float → Float) :
    ⦃⌜True⌝⦄
    ufunc_identity op
    ⦃⇓result => ⌜match result with
      | some id => ∀ x : Float, op x id = x ∧ op id x = x
      | none => ¬∃ id : Float, ∀ x : Float, op x id = x ∧ op id x = x⌝⦄ := by
  sorry
-- </vc-theorems>