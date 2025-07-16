import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Compute tangent element-wise. Equivalent to sin(x)/cos(x) element-wise. -/
def tan {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

/-- Specification: tan computes the tangent of each element, equivalent to sin(x)/cos(x),
    and is undefined when cos(x) = 0 (i.e., x = π/2 + kπ for integer k) -/
theorem tan_spec {n : Nat} (x : Vector Float n) 
    (h_valid : ∀ i : Fin n, Float.cos (x.get i) ≠ 0) :
    ⦃⌜∀ i : Fin n, Float.cos (x.get i) ≠ 0⌝⦄
    tan x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.tan (x.get i) ∧ 
                                result.get i = Float.sin (x.get i) / Float.cos (x.get i)⌝⦄ := by
  sorry
