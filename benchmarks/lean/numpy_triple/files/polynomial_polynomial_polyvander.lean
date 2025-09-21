-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    polyvander x deg
    ⦃⇓V => ⌜∀ i : Fin n, 
             (V.get i).get ⟨0, Nat.zero_lt_succ deg⟩ = 1.0 ∧ 
             (deg > 0 → (V.get i).get ⟨1, sorry⟩ = x.get i)⌝⦄ := by
  sorry
-- </vc-theorems>