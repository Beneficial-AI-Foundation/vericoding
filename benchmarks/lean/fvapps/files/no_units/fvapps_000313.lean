-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkIfCanBreak (s1 s2 : String) : Bool :=
  sorry

/- If two strings are compared with checkIfCanBreak, they must have same length -/
-- </vc-definitions>

-- <vc-theorems>
theorem check_if_can_break_same_length (s1 s2 : String) :
  checkIfCanBreak s1 s2 → String.length s1 = String.length s2 :=
  sorry
-- </vc-theorems>