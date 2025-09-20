-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.isInfixOf (sub : String) (str : String) : Bool := 
  sorry

variable (parse_html_code : String → String)

/- Single line comments are correctly identified and preserved --/
-- </vc-definitions>

-- <vc-theorems>
theorem single_line_comment_handling 
  (text : String)
  (h₁ : ¬ String.contains text '\n') :
  let comment := s!"<!--{text}-->"
  String.isInfixOf ">>> Single-line Comment" (parse_html_code comment) ∧ 
  (text.length > 0 → String.isInfixOf text (parse_html_code comment)) := sorry

/- Multi line comments are correctly identified and preserved --/

theorem multi_line_comment_handling 
  (text : String)
  (h₁ : String.contains text '\n') :
  let comment := s!"<!--{text}-->"
  String.isInfixOf ">>> Multi-line Comment" (parse_html_code comment) ∧
  (text.length > 0 → String.isInfixOf text (parse_html_code comment)) := sorry

/- Whitespace-only input results in empty output --/

theorem whitespace_handling 
  (s : String)
  (h₁ : ∀ c ∈ s.data, c = ' ' ∨ c = '\n' ∨ c = '\t') :
  parse_html_code s = "" := sorry

/- Empty input results in empty output --/

theorem empty_input_handling :
  parse_html_code "" = "" := sorry

/- Regular text is marked as data and preserved --/

theorem basic_data_handling :
  let input := "Hello World"
  String.isInfixOf ">>> Data" (parse_html_code input) ∧
  String.isInfixOf "Hello World" (parse_html_code input) := sorry
-- </vc-theorems>