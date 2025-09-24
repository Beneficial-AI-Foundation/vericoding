-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def argpartition {n : Nat} (a : Vector Float n) (kth : Fin n) : Id (Vector (Fin n) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem argpartition_spec {n : Nat} (a : Vector Float n) (kth : Fin n) :
    ⦃⌜True⌝⦄
    argpartition a kth
    ⦃⇓indices => ⌜
      -- The indices form a valid permutation of 0..n-1
      (∀ i : Fin n, ∃ j : Fin n, indices.get j = i) ∧
      (∀ i j : Fin n, i ≠ j → indices.get i ≠ indices.get j) ∧
      -- Partition property: all elements before kth position are ≤ kth element
      (∀ i : Fin n, i < kth → a.get (indices.get i) ≤ a.get (indices.get kth)) ∧
      -- Partition property: all elements after kth position are ≥ kth element
      (∀ i : Fin n, kth < i → a.get (indices.get kth) ≤ a.get (indices.get i))
    ⌝⦄ := by
  sorry
-- </vc-theorems>