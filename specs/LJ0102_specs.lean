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

-- <vc-definitions>
def removeDuplicates (arr : Array Int) (h_precond : removeDuplicates_precond (arr)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeDuplicates_postcond (arr : Array Int) (unique_arr : Array Int) (h_precond : removeDuplicates_precond (arr)) :=
  unique_arr.toList = arr.toList.filter (fun x => countFrequencyRcr arr.toList x = 1)

theorem removeDuplicates_spec_satisfied (arr : Array Int) (h_precond : removeDuplicates_precond (arr)) :
    removeDuplicates_postcond (arr) (removeDuplicates (arr) h_precond) h_precond := by
  sorry
-- </vc-theorems>