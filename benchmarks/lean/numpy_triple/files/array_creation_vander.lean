-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vander {n m : Nat} (x : Vector Float n) : Id (Vector (Vector Float m) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vander_spec {n m : Nat} (x : Vector Float n) (h_m_pos : m > 0) :
    ⦃⌜m > 0⌝⦄
    vander x
    ⦃⇓result => ⌜∀ (i : Fin n) (j : Fin m), 
                  (result.get i).get j = (x.get i) ^ ((m - 1 - j.val).toFloat)⌝⦄ := by
  sorry
-- </vc-theorems>