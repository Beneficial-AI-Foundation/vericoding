/-  Hermite series whose graph is a straight line.

    Creates a Hermite series representation for the line off + scl*x.
    Returns a 2-element vector where:
    - First element is the constant term (off)
    - Second element is the linear coefficient (scl/2)

    Note: When scl = 0, the second element is 0, representing a constant function.
-/

/-  Specification: hermline returns Hermite coefficients for a linear function.

    The Hermite series representation of off + scl*x has coefficients:
    - c₀ = off (constant term)
    - c₁ = scl/2 (linear term coefficient)

    These coefficients, when evaluated as a Hermite series, produce the 
    original linear function. The relationship comes from the fact that
    H₁(x) = 2x in the physicist's Hermite polynomials.
-/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def hermline (off scl : Float) : Id (Vector Float 2) :=
  sorry

theorem hermline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    hermline off scl
    ⦃⇓result => ⌜
      result.get ⟨0, by decide⟩ = off ∧
      result.get ⟨1, by decide⟩ = scl / 2
    ⌝⦄ := by
  sorry
