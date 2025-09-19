-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : String := sorry 

theorem solve_preserves_length (s : String) : 
  s.length = (solve s).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_preserves_spaces (s : String) (i : String.Pos) :
  (s.get i = ' ') = ((solve s).get i = ' ') := sorry
-- </vc-theorems>