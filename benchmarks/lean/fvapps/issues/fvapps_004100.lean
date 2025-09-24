-- <vc-preamble>
def display_board (board : List String) (width : Nat) : String := sorry

def getEvenElements (xs : List α) : List α :=
  xs.enum.filter (fun (i, _) => i % 2 = 0) |>.map Prod.snd
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getOddElements (xs : List α) : List α :=
  xs.enum.filter (fun (i, _) => i % 2 = 1) |>.map Prod.snd
-- </vc-definitions>

-- <vc-theorems>
theorem display_board_properties {board : List String} {width : Nat} 
  (h1 : ∀ x, x ∈ board → (x = "X" ∨ x = "O" ∨ x = " "))
  (h2 : 0 < width)
  (h3 : width ≤ 10) 
  (h4 : board.length % width = 0) :
  let result := display_board board width
  let lines := result.splitOn "\n"
  let content_lines := getEvenElements lines
  ∃ line_length : Nat,
    -- All content lines have same width
    (∀ l ∈ content_lines, l.length = line_length) ∧
    -- Correct number of separators between cells 
    (∀ l ∈ content_lines, (l.toList.filter (· = '|')).length = width - 1) ∧
    -- Each cell is at most 3 chars wide
    (∀ l ∈ content_lines, ∀ cell ∈ (l.splitOn "|").map String.trim, cell.length ≤ 3) ∧
    -- Separator lines are correct length
    (lines.length > 1 → 
      ∀ l ∈ getOddElements lines, l = String.mk (List.replicate (4*width - 1) '-')) := sorry

theorem width_one_no_pipes {board : List String}
  (h1 : ∀ x, x ∈ board → (x = "X" ∨ x = "O" ∨ x = " "))
  (h2 : 0 < board.length) :
  ¬(display_board board 1).contains '|' := sorry
-- </vc-theorems>