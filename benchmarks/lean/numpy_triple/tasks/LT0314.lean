-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_floor {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_floor_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_floor x
    ⦃⇓result => ⌜∀ i : Fin n,
      (∃ k : Int, result.get i = Float.ofInt k) ∧
      result.get i ≤ x.get i ∧
      x.get i < result.get i + 1 ∧
      (∀ k : Int, Float.ofInt k ≤ x.get i → Float.ofInt k ≤ result.get i) ∧
      (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j) ∧
      (∃ k : Int, result.get i = Float.ofInt k → (result.get i).floor = result.get i) ∧
      result.get i = -((-x.get i).ceil) ∧
      (∃ k : Int, x.get i = Float.ofInt k → result.get i = x.get i)⌝⦄ := by
  sorry
-- </vc-theorems>