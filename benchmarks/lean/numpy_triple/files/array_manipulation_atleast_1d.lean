import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def atleast_1d {n : Nat} (arr : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem atleast_1d_spec {n : Nat} (arr : Vector Float n) :
    ⦃⌜True⌝⦄
    atleast_1d arr
    ⦃⇓result => ⌜result = arr ∧ (∀ i : Fin n, result.get i = arr.get i)⌝⦄ := by
  sorry
