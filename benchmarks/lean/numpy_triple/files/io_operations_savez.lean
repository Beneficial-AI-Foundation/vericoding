-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def savez {n m : Nat} (file : String) (arr1 : Vector Float n) (arr2 : Vector Float m) 
    (allow_pickle : Bool := true) : Id Unit :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem savez_spec {n m : Nat} (file : String) (arr1 : Vector Float n) (arr2 : Vector Float m) 
    (allow_pickle : Bool := true) 
    (h_writable : True) (h_valid_path : True) :
    ⦃⌜True⌝⦄
    savez file arr1 arr2 allow_pickle
    ⦃⇓result => ⌜result = () ∧ 
                  (∃ (archive_exists : Bool), archive_exists = true) ∧
                  (∃ (recoverable_arr1 : Vector Float n), 
                    (∀ i : Fin n, recoverable_arr1.get i = arr1.get i)) ∧
                  (∃ (recoverable_arr2 : Vector Float m), 
                    (∀ i : Fin m, recoverable_arr2.get i = arr2.get i)) ∧
                  (∃ (file_size : Nat), file_size > 0)⌝⦄ := by
  sorry
-- </vc-theorems>