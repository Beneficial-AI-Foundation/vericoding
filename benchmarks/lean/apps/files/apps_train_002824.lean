-- <vc-helpers>
-- </vc-helpers>

def get_middle : String → String 
| s => sorry

theorem middle_length_property (s : String) (h : s.length > 0) : 
  let result := get_middle s
  result.length = if s.length % 2 = 0 then 2 else 1 := 
sorry

theorem single_char_property (s : String) (h : s.length = 1) :
  get_middle s = s :=
sorry

theorem middle_position_property (s : String) (h : s.length > 1) :
  let result := get_middle s
  let mid := (s.length - 1) / 2
  ∃ pos : String.Pos, get_middle s = s.extract pos (⟨mid + result.length⟩) :=
sorry

/-
info: 'es'
-/
-- #guard_msgs in
-- #eval get_middle "test"

/-
info: 't'
-/
-- #guard_msgs in
-- #eval get_middle "testing"

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval get_middle "A"

-- Apps difficulty: introductory
-- Assurance level: unguarded