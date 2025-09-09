import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def matrix_norm {rows cols : Nat} (x : Vector (Vector Float cols) rows) : Id Float :=
  sorry

theorem matrix_norm_spec {rows cols : Nat} (x : Vector (Vector Float cols) rows) :
    ⦃⌜True⌝⦄
    matrix_norm x
    ⦃⇓res => ⌜res ≥ 0 ∧ 
             (res = 0 ↔ ∀ i : Fin rows, ∀ j : Fin cols, (x.get i).get j = 0) ∧
             (∀ i : Fin rows, ∀ j : Fin cols, Float.abs ((x.get i).get j) ≤ res) ∧
             (rows > 0 ∧ cols > 0 → 
               ∃ i : Fin rows, ∃ j : Fin cols, (x.get i).get j ≠ 0 → res > 0)⌝⦄ := by
  sorry
