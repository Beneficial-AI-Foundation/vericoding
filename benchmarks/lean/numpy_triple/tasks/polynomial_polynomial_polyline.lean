-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def polyline (off scl : Float) : Id (Vector Float 2) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem polyline_spec (off scl : Float) :
    ⦃⌜True⌝⦄
    polyline off scl
    ⦃⇓result => ⌜
        -- Constant term is always off
        result.get ⟨0, by omega⟩ = off ∧

        -- Linear coefficient is always scl
        result.get ⟨1, by omega⟩ = scl ∧

        -- Size is always 2 (representing up to degree 1 polynomial)
        result.toList.length = 2 ∧

        -- Mathematical property: this represents the polynomial off + scl*x
        -- When evaluated at x=0, gives off
        result.get ⟨0, by omega⟩ = off ∧

        -- The derivative coefficient is scl
        result.get ⟨1, by omega⟩ = scl ∧

        -- Example evaluation: if we evaluate at x=1, we get off + scl
        -- (This is a mathematical property of the polynomial representation)
        result.get ⟨0, by omega⟩ + result.get ⟨1, by omega⟩ = off + scl
    ⌝⦄ := by
  sorry
-- </vc-theorems>