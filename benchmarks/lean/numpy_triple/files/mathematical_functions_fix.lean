-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_fix {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_fix_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_fix x
    ⦃⇓result => ⌜∀ i : Fin n,
      (∃ k : Int, result.get i = Float.ofInt k) ∧
      (result.get i).abs ≤ (x.get i).abs ∧
      (x.get i ≥ 0 → result.get i ≥ 0) ∧
      (x.get i ≤ 0 → result.get i ≤ 0) ∧
      (x.get i - result.get i).abs < 1 ∧
      (x.get i ≥ 0 → result.get i = (x.get i).floor) ∧
      (x.get i < 0 → result.get i = (x.get i).ceil) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (∀ j : Fin n, x.get i ≤ x.get j → result.get i ≤ result.get j)⌝⦄ := by
  sorry
-- </vc-theorems>