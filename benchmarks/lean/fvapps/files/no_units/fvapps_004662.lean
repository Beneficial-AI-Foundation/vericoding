-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lineup_students (input : String) : List String := sorry

/-
  lineupStudentsLengthPreserved:
  For any list of students, the length of the output list
  equals the length of the input list
-/
-- </vc-definitions>

-- <vc-theorems>
theorem lineupStudentsLengthPreserved (input : String) (names : List String) :
  names = lineup_students input → 
  (lineup_students input).length = names.length := sorry
-- </vc-theorems>