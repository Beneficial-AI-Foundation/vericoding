-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkered_board (n : Int) : String := sorry

/- For valid inputs (n ≥ 2), checkered_board produces a string with:
    1. n rows
    2. n columns in each row
    3. Alternating pattern of □ and ■ where:
       - For even n, top-left is □
       - For odd n, top-left is ■ -/
-- </vc-definitions>

-- <vc-theorems>
theorem valid_board_pattern (n : Int) (h : n ≥ 2) :
  let result := checkered_board n
  let rows := result.splitOn "\n"
  (result.isEmpty = false) ∧ 
  (rows.length = n) ∧ 
  (∀ row ∈ rows, (row.splitOn " ").length = n) ∧
  (∀ (i j : Nat), i < n.toNat → j < n.toNat → 
    ((rows.get! i).splitOn " ").get! j = 
      if ((i : Int) + j) % 2 = n % 2 
      then "■" 
      else "□") := sorry

/- For invalid inputs (n ≤ 1), checkered_board returns false -/

theorem invalid_inputs (n : Int) (h : n ≤ 1) :
  checkered_board n = "false" := sorry

end CheckeredBoard

/-
info: '■ □ ■ □ ■\n□ ■ □ ■ □\n■ □ ■ □ ■\n□ ■ □ ■ □\n■ □ ■ □ ■'
-/
-- #guard_msgs in
-- #eval checkered_board 5

/-
info: '■ □ ■\n□ ■ □\n■ □ ■'
-/
-- #guard_msgs in
-- #eval checkered_board 3

/-
info: '□ ■\n■ □'
-/
-- #guard_msgs in
-- #eval checkered_board 2

/-
info: False
-/
-- #guard_msgs in
-- #eval checkered_board 1

/-
info: False
-/
-- #guard_msgs in
-- #eval checkered_board -1

/-
info: False
-/
-- #guard_msgs in
-- #eval checkered_board "test"

/-
info: False
-/
-- #guard_msgs in
-- #eval checkered_board None
-- </vc-theorems>