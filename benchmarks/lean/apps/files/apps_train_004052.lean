-- <vc-helpers>
-- </vc-helpers>

def pattern (n : Int) : String := sorry

theorem pattern_nonpos {n : Int} (h : n ≤ 0) : 
  pattern n = "" := sorry

theorem pattern_line_structure {n : Int} (h : n > 0) (i : Nat) (h2 : i < n) :
  let lines := (pattern n).splitOn "\n"
  let expected_num := 2 * i + 1
  lines[i]! = String.mk (List.replicate expected_num (toString expected_num).data[0]!) := sorry

theorem pattern_examples : 
  pattern 0 = "" ∧ 
  pattern (-1) = "" ∧
  pattern 4 = "1\n333" ∧
  pattern 5 = "1\n333\n55555" := sorry

/-
info: '1\n333'
-/
-- #guard_msgs in
-- #eval pattern 4

/-
info: '1\n333\n55555'
-/
-- #guard_msgs in
-- #eval pattern 5

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern 0

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern -5

-- Apps difficulty: introductory
-- Assurance level: unguarded