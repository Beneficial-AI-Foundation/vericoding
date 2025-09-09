import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def argsort {n : Nat} (a : Vector Float n) : Id (Vector (Fin n) n) :=
  sorry

theorem argsort_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    argsort a
    ⦃⇓indices => ⌜-- The result is a permutation of all indices
                   (∀ i : Fin n, ∃ j : Fin n, indices.get j = i) ∧
                   (∀ i j : Fin n, indices.get i = indices.get j → i = j) ∧
                   -- The indices produce a sorted sequence
                   (∀ i j : Fin n, i < j → a.get (indices.get i) ≤ a.get (indices.get j)) ∧
                   -- For equal elements, maintain relative order (stable sort)
                   (∀ i j : Fin n, i < j → a.get (indices.get i) = a.get (indices.get j) → indices.get i < indices.get j)⌝⦄ := by
  sorry
