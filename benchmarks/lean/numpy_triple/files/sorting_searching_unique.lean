import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def unique {n : Nat} (ar : Vector Float n) : Id (Σ m : Nat, Vector Float m) :=
  sorry

theorem unique_spec {n : Nat} (ar : Vector Float n) :
    ⦃⌜True⌝⦄
    unique ar
    ⦃⇓result => ⌜let m := result.1
                  let unique_arr := result.2
                  -- The result is sorted in ascending order
                  (∀ i j : Fin m, i < j → unique_arr.get i < unique_arr.get j) ∧
                  -- No duplicates in the result
                  (∀ i j : Fin m, i ≠ j → unique_arr.get i ≠ unique_arr.get j) ∧
                  -- Every element in result comes from the input array
                  (∀ i : Fin m, ∃ j : Fin n, unique_arr.get i = ar.get j) ∧
                  -- Every distinct element from input appears in result
                  (∀ i : Fin n, ∃ j : Fin m, ar.get i = unique_arr.get j)⌝⦄ := by
  sorry
