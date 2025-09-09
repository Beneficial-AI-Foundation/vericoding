import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def c_ {n : Nat} (arr1 arr2 : Vector Float n) : Id (Vector (Vector Float 2) n) :=
  sorry

theorem c_spec {n : Nat} (arr1 arr2 : Vector Float n) :
    ⦃⌜True⌝⦄
    c_ arr1 arr2
    ⦃⇓result => ⌜∀ i : Fin n, 
      result.get i = ⟨#[arr1.get i, arr2.get i], by simp⟩⌝⦄ := by
  sorry
