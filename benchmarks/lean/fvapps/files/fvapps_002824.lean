-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_middle : String → String 
| s => sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>