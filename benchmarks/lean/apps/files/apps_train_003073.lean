-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def robotTransfer : List (List String) → Nat → Nat := sorry

def parseCoords (s : String) : Option (Nat × Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem robotTransfer_2x2_valid_output 
  (matrix : List (List String)) 
  (k : Nat) 
  (h1 : matrix.length = 2)
  (h2 : ∀ row ∈ matrix, row.length = 2)
  (h3 : ∀ row ∈ matrix, ∀ cell ∈ row, 
    match parseCoords cell with
    | some (x, y) => x ≤ 1 ∧ y ≤ 1
    | none => False)
  (h4 : 1 ≤ k ∧ k ≤ 10)
  : 0 ≤ robotTransfer matrix k ∧ robotTransfer matrix k ≤ 4 := sorry

theorem robotTransfer_2x2_valid_matrix_format
  (matrix : List (List String)) 
  (h1 : matrix.length = 2)
  (h2 : ∀ row ∈ matrix, row.length = 2)
  : ∀ row ∈ matrix, ∀ cell ∈ row,
    match parseCoords cell with
    | some (x, y) => x ≤ 1 ∧ y ≤ 1
    | none => False := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval robot_transfer [["0,1", "0,0", "1,2"], ["1,1", "1,0", "0,2"], ["2,1", "2,0", "0,0"]] 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval robot_transfer [["0,1", "0,0"], ["1,1", "1,0"]] 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded