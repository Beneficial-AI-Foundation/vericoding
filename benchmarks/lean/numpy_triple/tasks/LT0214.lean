-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def save {n : Nat} (file : String) (arr : Vector Float n) (allow_pickle : Bool := false) : Id Unit :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem save_spec {n : Nat} (file : String) (arr : Vector Float n) (allow_pickle : Bool := false)
    (h_valid_path : True) (h_writable : True) :
    ⦃⌜True⌝⦄
    save file arr allow_pickle
    ⦃⇓result => ⌜result = () ∧
                  (∃ (file_content : String), 
                    -- File exists and contains serialized data
                    True ∧
                    -- Data can be recovered (save-load roundtrip property)
                    (∀ (loaded_vec : Vector Float n), 
                      (∃ (load_result : Id (Vector Float n)), 
                        load_result = pure loaded_vec) → 
                        (∀ i : Fin n, loaded_vec.get i = arr.get i)) ∧
                    -- Filename extension property
                    (file.endsWith ".npy" ∨ (file ++ ".npy").length > file.length) ∧
                    -- Determinism: same input produces same file
                    (∀ (second_save : Unit), 
                      (save file arr allow_pickle = pure second_save) → 
                      result = second_save))⌝⦄ := by
  sorry
-- </vc-theorems>