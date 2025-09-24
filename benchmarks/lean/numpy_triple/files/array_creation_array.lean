-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array (data : List Float) : Id (Vector Float data.length) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_spec (data : List Float) :
    ⦃⌜True⌝⦄
    array data
    ⦃⇓result => ⌜∀ i : Fin data.length, result.get i = data.get i⌝⦄ := by
  sorry
-- </vc-theorems>