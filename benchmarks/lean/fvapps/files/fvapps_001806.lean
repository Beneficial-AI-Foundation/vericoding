-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_word_ladders (begin_word end_word : String) (word_list : List String) : List (List String) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_list (begin_word end_word : String) (word_list : List String) :
  ∃ result, find_word_ladders begin_word end_word word_list = result := by
  sorry

theorem valid_path_properties (begin_word end_word : String) (word_list : List String) :
  ∀ path ∈ find_word_ladders begin_word end_word word_list,
    path.head? = some begin_word ∧ 
    path.getLast? = some end_word ∧
    (∀ w ∈ path, String.length w = String.length begin_word) ∧
    (∀ i < path.length - 1, 
      let w1 := path.get! i
      let w2 := path.get! (i+1)
      let chars1 := w1.data
      let chars2 := w2.data
      let diffs := (List.zip chars1 chars2).filter (fun p => p.fst ≠ p.snd)
      diffs.length = 1) ∧
    (∀ w ∈ path.tail, w ∈ word_list) := by
  sorry

theorem empty_result_when_end_not_in_wordlist (begin_word end_word : String) (word_list : List String) :
  end_word ∉ word_list → find_word_ladders begin_word end_word word_list = [] := by
  sorry

theorem all_paths_same_length (begin_word end_word : String) (word_list : List String) :
  let result := find_word_ladders begin_word end_word word_list
  result ≠ [] → ∃ n : Nat, ∀ path ∈ result, path.length = n := by
  sorry
-- </vc-theorems>