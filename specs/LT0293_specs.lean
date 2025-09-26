-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def clip {n : Nat} (arr : Vector Float n) (min_val max_val : Float) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem clip_spec {n : Nat} (arr : Vector Float n) (min_val max_val : Float) :
    ⦃⌜True⌝⦄
    clip arr min_val max_val
    ⦃⇓result => ⌜∀ i : Fin n, 
      (if min_val ≤ max_val then
        (if arr.get i < min_val then result.get i = min_val
         else if arr.get i > max_val then result.get i = max_val
         else result.get i = arr.get i)
      else 
        result.get i = max_val)⌝⦄ := by
  sorry
-- </vc-theorems>