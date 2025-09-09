import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polyfromroots {n : Nat} (roots : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry

theorem polyfromroots_spec {n : Nat} (roots : Vector Float n) :
    ⦃⌜True⌝⦄
    polyfromroots roots
    ⦃⇓coeffs => ⌜coeffs.get ⟨n, Nat.lt_succ_self n⟩ = 1 ∧
                 ∀ i : Fin n, ∃ (eval_poly : Float → Float), 
                   (∀ x : Float, eval_poly x = 0 ↔ x = roots.get i) ∧
                   eval_poly (roots.get i) = 0⌝⦄ := by
  sorry
