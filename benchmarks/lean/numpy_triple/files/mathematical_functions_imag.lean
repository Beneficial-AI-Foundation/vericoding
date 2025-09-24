-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def imag {n : Nat} (val : Vector (Float × Float) n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem imag_spec {n : Nat} (val : Vector (Float × Float) n) :
    ⦃⌜True⌝⦄
    imag val
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = (val.get i).2) ∧
                 (∀ i : Fin n, (val.get i).2 = 0 → result.get i = 0) ∧
                 (∀ i : Fin n, (val.get i).1 ≠ 0 ∨ (val.get i).2 ≠ 0 → 
                   result.get i = (val.get i).2) ∧
                 (∀ i : Fin n, ∀ (α : Float), 
                   let scaled_complex := (α * (val.get i).1, α * (val.get i).2)
                   result.get i = (val.get i).2 → 
                   α * result.get i = α * (val.get i).2)⌝⦄ := by
  sorry
-- </vc-theorems>