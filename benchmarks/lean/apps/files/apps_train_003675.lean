-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : String := sorry 

theorem solve_preserves_length (s : String) : 
  s.length = (solve s).length := sorry

theorem solve_preserves_spaces (s : String) (i : String.Pos) :
  (s.get i = ' ') = ((solve s).get i = ' ') := sorry

/-
info: 'srawedoc'
-/
-- #guard_msgs in
-- #eval solve "codewars"

/-
info: 'edoc ruoy'
-/
-- #guard_msgs in
-- #eval solve "your code"

/-
info: 'skco redo cruoy'
-/
-- #guard_msgs in
-- #eval solve "your code rocks"

-- Apps difficulty: introductory
-- Assurance level: unguarded