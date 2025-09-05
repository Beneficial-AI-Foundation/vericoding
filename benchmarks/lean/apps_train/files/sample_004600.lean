# Task
 Given two cells on the standard chess board, determine whether they have the same color or not.

# Example

 For `cell1 = "A1" and cell2 = "C3"`, the output should be `true`.
 For `cell1 = "A1" and cell2 = "H3"`, the output should be `false`.

# Input/Output

 - `[input]` string `cell1`

 - `[input]` string `cell2`

 - `[output]` a boolean value

    `true` if both cells have the same color, `false` otherwise.

def chess_board_cell_color : Cell → Cell → Bool := sorry

theorem chess_board_symmetry (c1 c2 : Cell) : 
  chess_board_cell_color c1 c2 = chess_board_cell_color c2 c1 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded