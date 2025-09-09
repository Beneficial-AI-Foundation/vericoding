import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def array (data : List Float) : Id (Vector Float data.length) :=
  sorry

theorem array_spec (data : List Float) :
    ⦃⌜True⌝⦄
    array data
    ⦃⇓result => ⌜∀ i : Fin data.length, result.get i = data.get i⌝⦄ := by
  sorry
