-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_bincount {n : Nat} (x : Vector Nat n) (max_val : Nat) 
    (h_bounds : ∀ i : Fin n, x.get i ≤ max_val) : Id (Vector Nat (max_val + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_bincount_spec {n : Nat} (x : Vector Nat n) (max_val : Nat) 
    (h_bounds : ∀ i : Fin n, x.get i ≤ max_val) :
    ⦃⌜∀ i : Fin n, x.get i ≤ max_val⌝⦄
    numpy_bincount x max_val h_bounds
    ⦃⇓result => ⌜∀ val : Fin (max_val + 1), 
                   result.get val = (x.toList.filter (· = val.val)).length⌝⦄ := by
  sorry
-- </vc-theorems>