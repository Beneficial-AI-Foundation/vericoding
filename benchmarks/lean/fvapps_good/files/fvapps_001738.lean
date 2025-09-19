-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_folder_names (names : List String) : List String := sorry

theorem get_folder_names_output_length 
    (names : List String) :
    List.length (get_folder_names names) = List.length names := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_folder_names_unique
    (names : List String) :
    List.Nodup (get_folder_names names) := sorry

theorem get_folder_names_original_preserved
    (names : List String)
    (i : Nat)
    (h : i < names.length) :
    let out := get_folder_names names
    have h' : i < out.length := by
      rw [get_folder_names_output_length names]
      exact h
    let orig := names[i]'h
    let gen := out[i]'h'
    (∀ (j : Nat) (hj : j < i), names[j]'(Nat.lt_trans hj h) ≠ orig) →
    (orig = gen ∨ ∃ n : Nat, gen = orig ++ "(" ++ n.repr ++ ")") := sorry
-- </vc-theorems>