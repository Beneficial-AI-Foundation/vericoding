-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def load {n : Nat} (file : String) (allow_pickle : Bool := false) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem load_spec {n : Nat} (file : String) (allow_pickle : Bool := false) 
    (h_file_exists : True) (h_valid_format : True) (h_compatible_size : True) :
    ⦃⌜True⌝⦄
    load file allow_pickle
    ⦃⇓result => ⌜result.toArray.size = n ∧ 
                  (∀ i : Fin n, ∃ (stored_val : Float), result.get i = stored_val) ∧
                  (∀ (second_load : Vector Float n), 
                    (load file allow_pickle = pure second_load) → 
                    (∀ i : Fin n, result.get i = second_load.get i))⌝⦄ := by
  sorry
-- </vc-theorems>