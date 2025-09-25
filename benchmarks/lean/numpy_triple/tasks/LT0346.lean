-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Batteries.Lean.Float
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nextafter {n : Nat} (x1 x2 : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nextafter_spec {n : Nat} (x1 x2 : Vector Float n) :
    ⦃⌜True⌝⦄
    nextafter x1 x2
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Identity case: when x1 equals x2, result equals x1
      (x1.get i = x2.get i → result.get i = x1.get i) ∧
      -- Direction consistency: result moves towards x2
      ((x1.get i < x2.get i → x1.get i < result.get i ∧ result.get i ≤ x2.get i) ∧
       (x1.get i > x2.get i → x1.get i > result.get i ∧ result.get i ≥ x2.get i)) ∧
      -- Minimal step property: result is the immediate next representable value
      ((x1.get i < x2.get i → ∀ y : Float, x1.get i < y ∧ y < result.get i → ¬(∃ z : Float, x1.get i < z ∧ z < y)) ∧
       (x1.get i > x2.get i → ∀ y : Float, result.get i < y ∧ y < x1.get i → ¬(∃ z : Float, y < z ∧ z < x1.get i))) ∧
      -- Finiteness preservation: if both inputs are finite, result is finite (unless at boundary)
      (Float.isFinite (x1.get i) ∧ Float.isFinite (x2.get i) ∧ x1.get i ≠ x2.get i → 
       Float.isFinite (result.get i) ∨ result.get i = Float.inf ∨ result.get i = -Float.inf)⌝⦄ := by
  sorry
-- </vc-theorems>