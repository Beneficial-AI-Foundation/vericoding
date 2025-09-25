-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_duplicates (s : String) : String := sorry

theorem result_is_subsequence (s : String) : 
  let result := remove_duplicates s
  ∃ indices : List String.Pos, 
    (∀ (i j : Fin indices.length), i.val < j.val → indices[i.val]! < indices[j.val]!) ∧ 
    indices.map (String.get s) = result.data := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_same_char_gives_empty_or_single (c : Char) (s : String) :
  (∀ i : String.Pos, s.get i = c) →
  remove_duplicates s = "" ∨ remove_duplicates s = String.mk [c] := sorry

theorem repeated_application_stable (s : String) :
  remove_duplicates (remove_duplicates s) = remove_duplicates s := sorry

theorem empty_string :
  remove_duplicates "" = "" := sorry

theorem non_letters_unchanged (s : String) :
  (∀ c ∈ s.data, ¬ c.isAlpha) →
  remove_duplicates s = s := sorry
-- </vc-theorems>