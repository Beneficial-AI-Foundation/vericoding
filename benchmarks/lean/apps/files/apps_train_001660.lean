-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_word (board : List (List Char)) (word : String) : Bool := sorry

theorem single_char_findable {board : List (List Char)} (h1 : board.length > 0) 
    (h2 : ∀ (row : List Char), row ∈ board → row.length > 0) 
    (h3 : ∀ (row₁ row₂ : List Char), row₁ ∈ board → row₂ ∈ board → row₁.length = row₂.length) :
  ∀ x y, x < board.length → y < (board.get! 0).length → 
    find_word board ((board.get! x).get! y).toString := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem long_word_not_findable {board : List (List Char)} (h1 : board.length > 0)
    (h2 : ∀ (row : List Char), row ∈ board → row.length > 0)
    (h3 : ∀ (row₁ row₂ : List Char), row₁ ∈ board → row₂ ∈ board → row₁.length = row₂.length)
    (word : String) :
  word.length > board.length * (board.get! 0).length →
    ¬(find_word board word) := sorry

theorem single_cell_board_theorems :
  find_word [['A']] "A" ∧
  ¬(find_word [['A']] "B") := sorry

theorem single_row_board_theorems :
  find_word [['A', 'B']] "AB" ∧
  find_word [['A', 'B']] "BA" := sorry

theorem single_column_board_theorems :
  find_word [['A'], ['B']] "AB" ∧
  find_word [['A'], ['B']] "BA" := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval find_word [["I", "L", "A", "W"], ["B", "N", "G", "E"], ["I", "U", "A", "O"], ["A", "S", "R", "L"]] "BINGO"

/-
info: False
-/
-- #guard_msgs in
-- #eval find_word board1 "BUNGIE"

/-
info: True
-/
-- #guard_msgs in
-- #eval find_word board1 "ILNBIA"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded