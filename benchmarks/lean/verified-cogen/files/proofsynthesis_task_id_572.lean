-- <vc-preamble>
/- Recursive helper function to count frequency -/
def countFrequencyRcr (seq : List Int) (key : Int) : Nat :=
  match seq with
  | [] => 0
  | head :: tail => 
      countFrequencyRcr tail key + (if head = key then 1 else 0)

/- Precondition for removeDuplicates -/
@[reducible, simp]
def removeDuplicates_precond (arr : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check removeDuplicates