-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def outer {m n : Nat} (op : Float → Float → Float) (a : Vector Float m) (b : Vector Float n) : 
    Id (Vector (Vector Float n) m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem outer_spec {m n : Nat} (op : Float → Float → Float) (a : Vector Float m) (b : Vector Float n) :
    ⦃⌜True⌝⦄
    outer op a b
    ⦃⇓result => ⌜
      -- Result has correct outer dimensions
      result.size = m ∧
      -- Each row has correct inner dimension
      (∀ i : Fin m, (result.get i).size = n) ∧
      -- Each element is the result of applying the operator to the corresponding pair
      (∀ i : Fin m, ∀ j : Fin n, (result.get i).get j = op (a.get i) (b.get j)) ∧
      -- Structural property: result represents all pairs from Cartesian product
      (∀ i : Fin m, ∀ j : Fin n, ∃ ai bj, ai = a.get i ∧ bj = b.get j ∧ (result.get i).get j = op ai bj)
    ⌝⦄ := by
  sorry
-- </vc-theorems>