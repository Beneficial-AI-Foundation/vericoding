-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_ceil {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_ceil_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_ceil x
    ⦃⇓result => ⌜∀ i : Fin n,
      (∃ k : Int, result.get i = Float.ofInt k) ∧
      result.get i ≥ x.get i ∧
      result.get i < x.get i + 1 ∧
      (∀ k : Int, x.get i ≤ Float.ofInt k → result.get i ≤ Float.ofInt k) ∧
      (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j) ∧
      result.get i = -((-x.get i).floor)⌝⦄ := by
  sorry
-- </vc-theorems>