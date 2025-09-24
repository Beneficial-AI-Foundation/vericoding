-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_text (lines : List String) : List String := sorry

theorem reverse_text_lines_length_eq_input {lines : List String} : 
  List.length (reverse_text lines) = List.length lines := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_text_all_alpha_or_space {lines : List String} :
  ∀ line ∈ reverse_text lines, ∀ c ∈ line.data, c.isAlpha ∨ c = ' ' := sorry

theorem reverse_text_word_all_alpha {lines : List String} :
  ∀ line ∈ reverse_text lines, ∀ word ∈ line.splitOn " ", 
    ∀ c ∈ word.data, c.isAlpha := sorry

theorem reverse_text_preserves_line_count {lines : List String} :
  ∀ input_line ∈ lines, ∃ output_line ∈ reverse_text lines,
    ∀ word ∈ output_line.splitOn " ", ∀ c ∈ word.data, c.isAlpha := sorry

theorem reverse_text_reverse_order {lines : List String} : 
  ∀ i, i < lines.length → 
    ∃ j, j < (reverse_text lines).length ∧ 
         j = lines.length - 1 - i ∧
         ∀ word ∈ ((reverse_text lines).get ⟨j, sorry⟩).splitOn " ",
           ∀ c ∈ word.data, c.isAlpha := sorry

theorem reverse_text_nonempty_line_count {lines : List String} :
  let result := reverse_text lines
  let result_lines := result.filter (fun l => l.trim ≠ "")
  let input_lines := lines.filter (fun l => ∃ c ∈ l.data, c.isAlpha)
  List.length result_lines = List.length input_lines := sorry
-- </vc-theorems>