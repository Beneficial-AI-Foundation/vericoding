-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Polynomial {n : Nat} (coef : Vector Float n) (domain : Vector Float 2) (window : Vector Float 2) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Polynomial_spec {n : Nat} (coef : Vector Float n) (domain : Vector Float 2) (window : Vector Float 2)
    (h_domain : domain.get 0 ≠ domain.get 1) (h_window : window.get 0 ≠ window.get 1) :
    ⦃⌜domain.get 0 ≠ domain.get 1 ∧ window.get 0 ≠ window.get 1⌝⦄
    Polynomial coef domain window
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = coef.get i ∧
                 (domain.get 1 - domain.get 0 ≠ 0) ∧
                 (window.get 1 - window.get 0 ≠ 0)⌝⦄ := by
  sorry
-- </vc-theorems>