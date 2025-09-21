-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Structure representing a complex number with float components -/
structure Complex where
  /-- The real part of the complex number -/
  real : Float
  /-- The imaginary part of the complex number -/
  imag : Float
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def iscomplex {n : Nat} (x : Vector Complex n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem iscomplex_spec {n : Nat} (x : Vector Complex n) :
    ⦃⌜True⌝⦄
    iscomplex x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = ((x.get i).imag ≠ 0.0)) ∧
                 (∀ i : Fin n, (x.get i).imag = 0.0 → result.get i = false) ∧
                 (∀ i : Fin n, (x.get i).imag ≠ 0.0 → result.get i = true) ∧
                 (∀ i : Fin n, result.get i = true → (x.get i).imag ≠ 0.0) ∧
                 (∀ i : Fin n, result.get i = false → (x.get i).imag = 0.0)⌝⦄ := by
  sorry
-- </vc-theorems>